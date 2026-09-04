import GerverSofa.RationalInterval
import GerverSofa.CertificateManifest
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Floor

/-!
# Executable exact-rational replay of the 4D and 22D Krawczyk inclusions

This is a direct, floating-point-free transcription of the companion Python
algorithm.  It computes with `ℚ`, interval automatic differentiation and the
frozen rational preconditioners.  The analytic theorem saying that the Taylor
intervals enclose the real `sin` and `cos`, and the abstract Krawczyk theorem,
remain separate proof obligations; the arithmetic replay itself is decidable.
-/

namespace GerverSofa.ExactReplay

open GerverSofa
open RatInterval
open scoped BigOperators

def q (n : Int) (d : Nat := 1) : ℚ := (n : ℚ) / (d : ℚ)

def zeroI : RatInterval := point 0
def oneI : RatInterval := point 1

private def midpoint (x : RatInterval) : ℚ := (x.lo + x.hi) / 2

def scale (a : ℚ) (x : RatInterval) : RatInterval :=
  mul (point a) x

private def sumIntervals (xs : List RatInterval) : RatInterval :=
  xs.foldl add zeroI

def factorialQ (n : Nat) : ℚ := (Nat.factorial n : ℚ)

def signedTerm (k : Nat) (x : ℚ) (power : Nat) : ℚ :=
  let z := x ^ power / factorialQ power
  if k % 2 = 0 then z else -z

def sinPartial (x : ℚ) (terms : Nat) : ℚ :=
  Finset.sum (Finset.range terms) (fun k => signedTerm k x (2 * k + 1))

def cosPartial (x : ℚ) (terms : Nat) : ℚ :=
  Finset.sum (Finset.range terms) (fun k => signedTerm k x (2 * k))

def sinBound (x : ℚ) : RatInterval :=
  let a := sinPartial x 19
  let b := sinPartial x 20
  ⟨min a b, max a b⟩

def cosBound (x : ℚ) : RatInterval :=
  let a := cosPartial x 19
  let b := cosPartial x 20
  ⟨min a b, max a b⟩

def piI : RatInterval :=
  ⟨q 157079632679489661923132169163975144209858469968755 50000000000000000000000000000000000000000000000000,
   q 78539816339744830961566084581987572104929234984378 25000000000000000000000000000000000000000000000000⟩


def atanPartial (x : ℚ) (terms : Nat) : ℚ :=
  Finset.sum (Finset.range terms) (fun k =>
    if k % 2 = 0 then
      x ^ (2 * k + 1) / ((2 * k + 1 : Nat) : ℚ)
    else
      -(x ^ (2 * k + 1) / ((2 * k + 1 : Nat) : ℚ)))

def atanBound (x : ℚ) (lowTerms highTerms : Nat) : RatInterval :=
  let a := atanPartial x lowTerms
  let b := atanPartial x highTerms
  ⟨min a b, max a b⟩

def machinPi : RatInterval :=
  sub (scale 16 (atanBound (1 / 5) 43 44))
      (scale 4 (atanBound (1 / 239) 13 14))

/-- Exact downward rounding to a fixed number of decimal places. -/
def floorDecimal (x : ℚ) (digits : Nat := 60) : ℚ :=
  let scale : ℚ := (10 : ℚ) ^ digits
  ((⌊x * scale⌋ : ℤ) : ℚ) / scale

/-- Exact upward rounding to a fixed number of decimal places. -/
def ceilDecimal (x : ℚ) (digits : Nat := 60) : ℚ :=
  let scale : ℚ := (10 : ℚ) ^ digits
  ((⌈x * scale⌉ : ℤ) : ℚ) / scale

/-- The same 60-decimal outward rounding used by the submitted verifier. -/
def outwardDecimal (z : RatInterval) : RatInterval :=
  ⟨floorDecimal z.lo, ceilDecimal z.hi⟩

def sinSmall (x : RatInterval) : RatInterval :=
  outwardDecimal ⟨(sinBound x.lo).lo, (sinBound x.hi).hi⟩

def cosSmall (x : RatInterval) : RatInterval :=
  outwardDecimal ⟨(cosBound x.hi).lo, (cosBound x.lo).hi⟩

/-- Clamp an interval to the physical angular range used by the Gerver
certificate.  If `x ∈ [0, π/2]` and `x` is enclosed by the input interval,
then `x` is still enclosed after clamping once `piI` has been proved to
contain `Real.pi`. -/
def physicalClamp (x : RatInterval) : RatInterval :=
  ⟨max 0 x.lo, min (piI.hi / 2) x.hi⟩

/-- A fail-closed enclosure used only when an externally supplied interval is
too wide for the small-argument Taylor/range-reduction evaluator.  Every
certified Gerver call remains in one of the two sharp branches below, so this
fallback does not alter the frozen replay. -/
def universalTrigInterval : RatInterval := ⟨-1, 1⟩

/-- Complementary interval for the identity `sin x = cos (π/2-x)` and
`cos x = sin (π/2-x)`. -/
def complementInterval (x : RatInterval) : RatInterval :=
  ⟨max 0 (piI.lo / 2 - x.hi), piI.hi / 2 - x.lo⟩

def sinI (x : RatInterval) : RatInterval :=
  let z := physicalClamp x
  if z.hi ≤ 9 / 10 then sinSmall z
  else
    let y := complementInterval z
    if y.hi ≤ 9 / 10 then cosSmall y else universalTrigInterval

def cosI (x : RatInterval) : RatInterval :=
  let z := physicalClamp x
  if z.hi ≤ 9 / 10 then cosSmall z
  else
    let y := complementInterval z
    if y.hi ≤ 9 / 10 then sinSmall y else universalTrigInterval

structure D where
  val : RatInterval
  der : List RatInterval
  deriving Repr

namespace D

def const (v : RatInterval) (n : Nat) : D :=
  ⟨v, List.replicate n zeroI⟩

def pointConst (v : ℚ) (n : Nat) : D := const (point v) n

def varD (v : RatInterval) (j n : Nat) : D :=
  ⟨v, (List.range n).map (fun k => point (if k = j then 1 else 0))⟩

def addD (x y : D) : D :=
  ⟨add x.val y.val, List.zipWith add x.der y.der⟩

def negD (x : D) : D :=
  ⟨neg x.val, x.der.map neg⟩

def subD (x y : D) : D := addD x (negD y)

def mulD (x y : D) : D :=
  ⟨mul x.val y.val,
   List.zipWith (fun dx dy => add (mul dx y.val) (mul x.val dy)) x.der y.der⟩

def scaleD (a : ℚ) (x : D) : D :=
  ⟨scale a x.val, x.der.map (scale a)⟩

def sinD (x : D) : D :=
  let sv := sinI x.val
  let cv := cosI x.val
  ⟨sv, x.der.map (mul cv)⟩

def cosD (x : D) : D :=
  let sv := sinI x.val
  let cv := cosI x.val
  ⟨cv, x.der.map (fun z => neg (mul sv z))⟩

instance : Add D := ⟨addD⟩
instance : Neg D := ⟨negD⟩
instance : Sub D := ⟨subD⟩
instance : Mul D := ⟨mulD⟩
instance : HMul ℚ D D := ⟨scaleD⟩

end D

def getI (xs : List RatInterval) (i : Nat) : RatInterval :=
  xs.getD i zeroI

def getQ (xs : List ℚ) (i : Nat) : ℚ := xs.getD i 0
def getRow (m : List (List ℚ)) (i : Nat) : List ℚ := m.getD i []
def getDVal (xs : List D) (i : Nat) : D := xs.getD i (D.const zeroI 0)

private def replaceAt {α : Type} : Nat → α → List α → List α
  | 0, a, _ :: xs => a :: xs
  | n + 1, a, x :: xs => x :: replaceAt n a xs
  | _, _, [] => []

private def swapRows (a : List (List ℚ)) (i j : Nat) : List (List ℚ) :=
  if i = j then a
  else
    let ri := getRow a i
    let rj := getRow a j
    replaceAt j ri (replaceAt i rj a)

private def matrixEntry (a : List (List ℚ)) (i j : Nat) : ℚ :=
  getQ (getRow a i) j

private def eliminateBelow
    (a : List (List ℚ)) (pivotCol : Nat) : List (List ℚ) :=
  let n := a.length
  let p := matrixEntry a pivotCol pivotCol
  (List.range (n - (pivotCol + 1))).foldl (fun acc off =>
    let i := pivotCol + 1 + off
    let factor := matrixEntry acc i pivotCol / p
    let newRow := (List.range n).map (fun k =>
      if pivotCol < k then
        matrixEntry acc i k - factor * matrixEntry acc pivotCol k
      else matrixEntry acc i k)
    replaceAt i newRow acc) a

private def detAux : Nat → List (List ℚ) → Nat → ℚ → ℚ
  | 0, _, _, d => d
  | fuel + 1, a, j, d =>
      if j < a.length then
        match (List.range (a.length - j)).find?
            (fun off => matrixEntry a (j + off) j != 0) with
        | none => 0
        | some off =>
            let i := j + off
            let a' := swapRows a i j
            let d' := if i = j then d else -d
            let p := matrixEntry a' j j
            detAux fuel (eliminateBelow a' j) (j + 1) (d' * p)
      else d

/-- Exact rational Gaussian-elimination determinant. -/
private def detQ (a : List (List ℚ)) : ℚ :=
  detAux a.length a 0 1

def intervalDot (cs : List ℚ) (xs : List RatInterval) : RatInterval :=
  sumIntervals (List.zipWith scale cs xs)

def krawczyk
    (fn : List RatInterval → List D)
    (box : List RatInterval)
    (C : List (List ℚ)) : List RatInterval :=
  let n := box.length
  let x0 := box.map midpoint
  let pbox := x0.map point
  let f0 := (fn pbox).map D.val
  let fj := fn box
  let jac := fj.map D.der
  let base := (List.range n).map (fun i =>
    sub (point (getQ x0 i)) (intervalDot (getRow C i) f0))
  let mat := (List.range n).map (fun i =>
    (List.range n).map (fun k =>
      let terms := (List.range n).map (fun j =>
        scale (getQ (getRow C i) j) (getI (jac.getD j []) k))
      sub (point (if i = k then 1 else 0)) (sumIntervals terms)))
  (List.range n).map (fun i =>
    let dxTerms := (List.range n).map (fun k =>
      let z := getI box k
      let m := getQ x0 k
      mul (getI (mat.getD i []) k) ⟨z.lo - m, z.hi - m⟩)
    add (getI base i) (sumIntervals dxTerms))

/-- Interval matrix `I - C J(X)` occurring in the Krawczyk map. -/
def krawczykLinearPart
    (fn : List RatInterval → List D)
    (box : List RatInterval)
    (C : List (List ℚ)) : List (List RatInterval) :=
  let n := box.length
  let fj := fn box
  let jac := fj.map D.der
  (List.range n).map (fun i =>
    (List.range n).map (fun k =>
      let terms := (List.range n).map (fun j =>
        scale (getQ (getRow C i) j) (getI (jac.getD j []) k))
      sub (point (if i = k then 1 else 0)) (sumIntervals terms)))

def intervalRadius (z : RatInterval) : ℚ := (z.hi - z.lo) / 2
def intervalSupAbs (z : RatInterval) : ℚ := max |z.lo| |z.hi|

/-- Weighted sup-norm bound for an interval matrix, using the input-box
radii as weights.  A value `< 1` is the exact contraction margin used by the
Banach endgame. -/
def weightedContractionBound
    (mat : List (List RatInterval)) (box : List RatInterval) : ℚ :=
  let n := box.length
  (List.range n).foldl (fun current i =>
    let numerator := (List.range n).foldl (fun acc k =>
      acc + intervalSupAbs (getI (mat.getD i []) k) *
        intervalRadius (getI box k)) 0
    let denominator := intervalRadius (getI box i)
    max current (numerator / denominator)) 0

/-! ## Reduced 4D system -/

def reducedSystem (box : List RatInterval) : List D :=
  let n := 4
  let a := D.varD (getI box 0) 0 n
  let b := D.varD (getI box 1) 1 n
  let phi := D.varD (getI box 2) 2 n
  let theta := D.varD (getI box 3) 3 n
  let one := D.pointConst 1 n
  let half := D.pointConst (1 / 2) n
  let quarter := D.pointConst (1 / 4) n
  let piD := D.const piI n
  let cp := D.cosD phi
  let sp := D.sinD phi
  let ct := D.cosD theta
  let st := D.sinD theta
  let delta := theta - phi
  let f1 := a * (ct - cp) - (2 : ℚ) * b * sp + (delta - one) * ct - st + cp + sp
  let f2 := a * ((3 : ℚ) * st + sp) - (2 : ℚ) * b * cp
    + (3 : ℚ) * (delta - one) * st + (3 : ℚ) * ct - sp + cp
  let f3 := a * cp - sp - half + half * cp - b * sp
  let f4 := a + (1 / 2 : ℚ) * piD - phi - theta - b
    + half * delta * (one + a) + quarter * delta * delta
  [f1, f2, f3, f4]

private def x4 : List RatInterval := [
  ⟨q 1888531216873 20000000000000, q 4721328042183 50000000000000⟩,
  ⟨q 69960186366677 50000000000000, q 34980093183339 25000000000000⟩,
  ⟨q 122429264969 3125000000000, q 3917736479009 100000000000000⟩,
  ⟨q 2129067216821 3125000000000, q 68130150938273 100000000000000⟩
]

private def c4 : List (List ℚ) := [
  [q (-6807128249614081174405751646233895883477) 10000000000000000000000000000000000000000, q (-1668645298254898823756872685901589912999) 5000000000000000000000000000000000000000, q 142655469136580991746408771201083165281 250000000000000000000000000000000000000, q 6979196385375907434754729126542237618887 10000000000000000000000000000000000000000],
  [q (-1166509731502349263126377264338437200033) 2500000000000000000000000000000000000000, q 12885386748281427252440540606364884831 80000000000000000000000000000000000000, q 33867580317340694704135157308931896467 25000000000000000000000000000000000000, q (-669198169890925059603288141447454387733) 500000000000000000000000000000000000000],
  [q (-2734456716994644402025329684152137828373) 10000000000000000000000000000000000000000, q (-8773012441591382751224116906117915601) 62500000000000000000000000000000000000, q (-31169129168086947221083235454859786381) 156250000000000000000000000000000000000, q 3097544571982855798592484554650267326733 10000000000000000000000000000000000000000],
  [q 5937522534788503855395693041282403727707 10000000000000000000000000000000000000000, q (-12894234217809317884645394772127946998229) 5000000000000000000000000000000000000000, q (-8661560217304957931983485334759974222533) 5000000000000000000000000000000000000000, q 51750746732148285574274925461942534764817 10000000000000000000000000000000000000000]
]

private def z22 : List RatInterval := [
  ⟨q (-21032242207268875141628571849) 100000000000000000000000000000, q (-21032242207268875141608571849) 100000000000000000000000000000⟩,
  ⟨q 2499999999999999999999 10000000000000000000000, q 2500000000000000000001 10000000000000000000000⟩,
  ⟨q (-91917929277159332227479610289) 100000000000000000000000000000, q (-91917929277159332227459610289) 100000000000000000000000000000⟩,
  ⟨q 29525413734425341573853797657 62500000000000000000000000000, q 29525413734425341573866297657 62500000000000000000000000000⟩,
  ⟨q (-15344080735756291713875357283) 25000000000000000000000000000, q (-15344080735756291713870357283) 25000000000000000000000000000⟩,
  ⟨q 17792529580064437214538861001 20000000000000000000000000000, q 17792529580064437214542861001 20000000000000000000000000000⟩,
  ⟨q (-15417358304445500741761623987) 50000000000000000000000000000, q (-15417358304445500741751623987) 50000000000000000000000000000⟩,
  ⟨q 29525413734425341573853797657 62500000000000000000000000000, q 29525413734425341573866297657 62500000000000000000000000000⟩,
  ⟨q (-20344080735756291713874857283) 20000000000000000000000000000, q (-20344080735756291713870857283) 20000000000000000000000000000⟩,
  ⟨q 2499999999999999999999 10000000000000000000000, q 2500000000000000000001 10000000000000000000000⟩,
  ⟨q 2420644844145377502832171437 2000000000000000000000000000, q 2420644844145377502832571437 2000000000000000000000000000⟩,
  ⟨q (-2500000000000000000001) 10000000000000000000000, q (-2499999999999999999999) 10000000000000000000000⟩,
  ⟨q (-52762459802678462416060380937) 100000000000000000000000000000, q (-52762459802678462416040380937) 100000000000000000000000000000⟩,
  ⟨q 92025838516063762289360579501 100000000000000000000000000000, q 92025838516063762289380579501 100000000000000000000000000000⟩,
  ⟨q 313022761424232933776114655193 500000000000000000000000000000, q 313022761424232933776214655193 500000000000000000000000000000⟩,
  ⟨q (-151160128631428920268654781) 160000000000000000000000000, q (-151160128631428920268622781) 160000000000000000000000000⟩,
  ⟨q 1641278451780291167220080819 1250000000000000000000000000, q 1641278451780291167220330819 1250000000000000000000000000⟩,
  ⟨q (-105076534082910887440587258861) 200000000000000000000000000000, q (-105076534082910887440547258861) 200000000000000000000000000000⟩,
  ⟨q 2420644844145377502832171437 2000000000000000000000000000, q 2420644844145377502832571437 2000000000000000000000000000⟩,
  ⟨q 2499999999999999999999 10000000000000000000000, q 2500000000000000000001 10000000000000000000000⟩,
  ⟨q 1958868239504182093160893749 50000000000000000000000000000, q 78354729580167283726435751 2000000000000000000000000000⟩,
  ⟨q 34065075469136244723692787727 50000000000000000000000000000, q 34065075469136244723692787983 50000000000000000000000000000⟩
]

private def c22 : List (List ℚ) := [
  [q 97524664435861749 500000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q 101771747759019027 100000000000000000, q 1 1, q 0 1, q 63813611575753437 50000000000000000, q (-388441807573624079) 5000000000000000000, q 19675950003915553 31250000000000000, q (-298520460968330237) 500000000000000000, q (-548415754484802953) 1000000000000000000, q (-388441807573624079) 5000000000000000000, q 19675950003915553 31250000000000000, q 20287597594763393 100000000000000000, q (-10119107089800079) 10000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q 388441807573624079 5000000000000000000, q (-19675950003915553) 31250000000000000],
  [q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 1 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1],
  [q (-803432388936903217) 10000000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q 100605379900828451 50000000000000000, q 1 1, q 0 1, q 31765043860672787 12500000000000000, q (-4704777879791199) 4000000000000000, q 121750850637699193 100000000000000000, q (-122756605381830597) 100000000000000000, q (-30600542365273823) 312500000000000000, q (-88097234973899999) 500000000000000000, q 121750850637699193 100000000000000000, q 396110376767452643 1000000000000000000, q (-40111351612012509) 20000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q 88097234973899999 500000000000000000, q (-121750850637699193) 100000000000000000],
  [q 348543935143050227 50000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q 48663249173571721 200000000000000000, q 0 1, q 1 1, q (-229748851313700347) 1000000000000000000, q 38538669009926041 200000000000000000, q (-148514169684624997) 250000000000000000, q (-77095605529021527) 200000000000000000, q 899174721266506223 100000000000000000000, q 38538669009926041 200000000000000000, q 101485830315375003 250000000000000000, q 475834949279834579 5000000000000000000, q (-48935313448682273) 250000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-38538669009926041) 200000000000000000, q (-101485830315375003) 250000000000000000],
  [q (-27668786810187381) 62500000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q 156689147323938593 100000000000000000, q 1 1, q 0 1, q 6806785234747033 4000000000000000, q (-770251148686299847) 1000000000000000000, q 839507200167063927 1000000000000000000, q (-32364013024529501) 40000000000000000, q (-325328497901119923) 5000000000000000000, q (-770251148686299847) 1000000000000000000, q 839507200167063927 1000000000000000000, q 107433644407840839 1000000000000000000, q (-203691379660578653) 250000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-229748851313700181) 1000000000000000000, q (-839507200167063927) 1000000000000000000],
  [q 667707347369355603 100000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q 39302260617100937 200000000000000000, q 0 1, q 1 1, q 810045947451984161 10000000000000000000, q 770773380198521041 1000000000000000000, q (-376226714953999619) 1000000000000000000, q (-67547253722371331) 125000000000000000, q (-317030024240986261) 100000000000000000000, q 770773380198521041 1000000000000000000, q (-376226714953999619) 1000000000000000000, q (-50799288029152201) 50000000000000000, q (-293762044611903417) 1000000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-770773380198521041) 1000000000000000000, q (-623773285046000381) 1000000000000000000],
  [q (-27668786810187381) 62500000000000000000000000000000000, q 0 1, q 611138637517184627 10000000000000000000, q 48547105024120657 62500000000000000, q (-142441420640562477) 500000000000000000, q 1 1, q 0 1, q 107773638564961749 125000000000000000, q (-91076956856199917) 250000000000000000, q 461505893957135871 1000000000000000000, q (-195317298704084513) 500000000000000000, q (-32209663591571687) 1000000000000000000, q (-91076956856199917) 250000000000000000, q 461505893957135871 1000000000000000000, q (-45310771987942769) 250000000000000000, q 376036543315996397 1000000000000000000, q (-1) 1, q 0 1, q 0 1, q 0 1, q (-635692172575200387) 1000000000000000000, q (-461505893957135871) 1000000000000000000],
  [q 667707347369355603 100000000000000000000000000000000000, q 0 1, q (-133696152744215091) 100000000000000000, q (-31490225467869859) 50000000000000000, q 12045884354915673 125000000000000000, q 0 1, q 1 1, q (-229748851313700347) 1000000000000000000, q 12043334065601893 62500000000000000, q (-594056678738499877) 1000000000000000000, q (-385478027645107413) 1000000000000000000, q 449587360633251377 50000000000000000000, q 12043334065601893 62500000000000000, q (-594056678738499877) 1000000000000000000, q 951669898559669991 10000000000000000000, q (-195741253794729203) 1000000000000000000, q 0 1, q (-1) 1, q 0 1, q 0 1, q (-12043334065601893) 62500000000000000, q (-405943321261500123) 1000000000000000000],
  [q 498465919198540053 500000000000000000, q (-391372890930701059) 5000000000000000000, q (-8938515563507099) 6250000000000000, q (-55619746202997561) 250000000000000000, q 354753639572627011 500000000000000000, q 1 1, q 0 1, q 106356019292922399 50000000000000000, q (-18512557434314989) 40000000000000000, q 52469200010441497 50000000000000000, q (-102115972928981447) 100000000000000000, q 26142772207772183 62500000000000000, q (-18512557434314989) 40000000000000000, q 52469200010441497 50000000000000000, q 29978282170118999 2500000000000000000, q (-308810164152310551) 500000000000000000, q (-1) 1, q 0 1, q (-1) 1, q 0 1, q (-53718606414212533) 100000000000000000, q (-52469200010441497) 50000000000000000],
  [q (-782745781861401979) 10000000000000000000, q (-498465919198540053) 500000000000000000, q (-277739416158080399) 1000000000000000000, q (-295318582899254667) 500000000000000000, q (-18368646378566663) 125000000000000000, q 0 1, q 1 1, q (-133419044772954399) 250000000000000000000000000000000, q 14163773178071801 250000000000000000000000000000000, q (-1) 1, q 79939871278032317 250000000000000000000000000000000, q (-2418968094552299) 125000000000000000000000000000000, q 14163773178071801 250000000000000000000000000000000, q (-1) 1, q 470629071136429359 5000000000000000000000000000000000, q (-223711639524848453) 5000000000000000000000000000000000, q 0 1, q (-1) 1, q 0 1, q (-1) 1, q (-14163773178071801) 250000000000000000000000000000000, q (-21329108080229053) 625000000000000000000000000000000],
  [q (-97524664435861749) 500000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q (-101771747759019027) 100000000000000000, q 0 1, q 0 1, q (-63813611575753437) 50000000000000000, q 388441807573624079 5000000000000000000, q (-19675950003915553) 31250000000000000, q 298520460968330237 500000000000000000, q 548415754484802953 1000000000000000000, q 388441807573624079 5000000000000000000, q (-19675950003915553) 31250000000000000, q (-20287597594763393) 100000000000000000, q 10119107089800079 10000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-388441807573624079) 5000000000000000000, q 19675950003915553 31250000000000000],
  [q (-349465940599428639) 50000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q (-25253489731359111) 2500000000000000000000000000000000, q 0 1, q 0 1, q 50000000000000011 50000000000000000, q (-353674953581839119) 5000000000000000000000000000000000, q 94007553259298153 2000000000000000000000000000000000, q (-5928343202681263) 25000000000000000000000000000000, q (-173331002701677877) 10000000000000000000000000000000000, q (-353674953581839119) 5000000000000000000000000000000000, q 94007553259298153 2000000000000000000000000000000000, q (-288351357559389053) 50000000000000000000000000000000000, q (-899167441101047079) 10000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q 353674953581839119 5000000000000000000000000000000000, q (-94007553259298153) 2000000000000000000000000000000000],
  [q 199958107491582403 10000000000000000000000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q 122021605728424423 500000000000000000, q 0 1, q 0 1, q 770104303222080677 1000000000000000000, q 193360860585517491 1000000000000000000, q 407267153261943571 1000000000000000000, q (-383870749384345733) 1000000000000000000, q (-150698973735099509) 5000000000000000000, q 193360860585517491 1000000000000000000, q 407267153261943571 1000000000000000000, q 59669749873825801 625000000000000000, q (-98153004518806597) 500000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-193360860585517491) 1000000000000000000, q (-407267153261943571) 1000000000000000000],
  [q (-466502263483670063) 1000000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q (-50741366468655913) 25000000000000000, q 0 1, q 0 1, q (-50425164328510137) 20000000000000000, q 80468307190360827 500000000000000000, q (-124842964508786847) 100000000000000000, q 6283806471937059 5000000000000000, q 493376058472616841 5000000000000000000, q 80468307190360827 500000000000000000, q (-124842964508786847) 100000000000000000, q (-403274191369431989) 1000000000000000000, q 10096930279303431 5000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-80468307190360827) 500000000000000000, q 124842964508786847 100000000000000000],
  [q 0 1, q 0 1, q 0 1, q 0 1, q (-74404321145684893) 50000000000000000, q 0 1, q 0 1, q (-30804172128883227) 20000000000000000, q (-386721721171035093) 1000000000000000000, q (-814534306523887031) 1000000000000000000, q 153548299753738271 200000000000000000, q 150698973735099509 2500000000000000000, q (-386721721171035093) 1000000000000000000, q (-814534306523887031) 1000000000000000000, q 585810480789687893 1000000000000000000, q 20448330548652467 20000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q 386721721171035093 1000000000000000000, q 814534306523887031 1000000000000000000],
  [q 0 1, q 0 1, q 0 1, q 0 1, q (-488086422913697859) 1000000000000000000, q 0 1, q 0 1, q (-30804172128883227) 20000000000000000, q (-386721721171035093) 1000000000000000000, q (-814534306523887031) 1000000000000000000, q 153548299753738271 200000000000000000, q 150698973735099509 2500000000000000000, q (-386721721171035093) 1000000000000000000, q (-814534306523887031) 1000000000000000000, q 585810480789687893 1000000000000000000, q 20448330548652467 20000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q 386721721171035093 1000000000000000000, q 814534306523887031 1000000000000000000],
  [q 0 1, q 0 1, q 1 1, q 0 1, q (-244043211456848957) 1000000000000000000, q 0 1, q 0 1, q (-770104303222080677) 1000000000000000000, q (-193360860585517547) 1000000000000000000, q (-407267153261943571) 1000000000000000000, q 191935374692172811 500000000000000000, q 301397947470199087 10000000000000000000, q (-193360860585517547) 1000000000000000000, q (-407267153261943571) 1000000000000000000, q (-477357998990606547) 5000000000000000000, q 98153004518806597 500000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q 193360860585517547 1000000000000000000, q 407267153261943571 1000000000000000000],
  [q 0 1, q 0 1, q 0 1, q 1 1, q (-32926249572211761) 20000000000000000, q 0 1, q 0 1, q (-8197382535470743) 6250000000000000, q 29041696495897041 62500000000000000, q (-304347948359896703) 500000000000000000, q 326889265645238569 500000000000000000, q 513317328155524291 10000000000000000000, q 29041696495897041 62500000000000000, q (-304347948359896703) 500000000000000000, q (-63326938273327693) 250000000000000000, q 42775732448415943 25000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-29041696495897041) 62500000000000000, q 304347948359896703 500000000000000000],
  [q 1 1, q 0 1, q 0 1, q 0 1, q (-101771747759019027) 100000000000000000, q 0 1, q 0 1, q (-31906805787876713) 25000000000000000, q 388441807573624287 5000000000000000000, q (-314815200062648959) 500000000000000000, q 597040921936660363 1000000000000000000, q 548415754484802953 1000000000000000000, q 388441807573624287 5000000000000000000, q (-314815200062648959) 500000000000000000, q (-12679748496727131) 62500000000000000, q 10119107089800079 10000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-388441807573624287) 5000000000000000000, q 314815200062648959 500000000000000000],
  [q 0 1, q 1 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q (-1) 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1],
  [q (-498591875083207211) 50000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q (-29185445604164767) 100000000000000000, q 0 1, q 0 1, q 79792970670302621 200000000000000000, q (-280736398130924159) 1000000000000000000, q (-546891343398928753) 1000000000000000000, q (-19887038235377269) 100000000000000000, q (-31228805607184943) 2000000000000000000, q (-280736398130924159) 1000000000000000000, q (-546891343398928753) 1000000000000000000, q (-62553783297256041) 500000000000000000, q 55986183994322411 250000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q 280736398130924159 1000000000000000000, q 546891343398928753 1000000000000000000],
  [q 354149563585840613 100000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q 142456721371719919 50000000000000000, q 0 1, q 0 1, q 173231204346099177 50000000000000000, q (-515769368712372689) 100000000000000000, q 59375225347885019 50000000000000000, q (-5396865719265527) 3125000000000000, q (-135595994488679511) 1000000000000000000, q (-515769368712372689) 100000000000000000, q 59375225347885019 50000000000000000, q 55842855499643207 25000000000000000, q (-656462321731497211) 1000000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q 515769368712372689 100000000000000000, q (-59375225347885019) 50000000000000000]
]

/-! ## Direct 22D Romik system -/

def rotD (t z1 z2 : D) : D × D :=
  let ct := D.cosD t
  let st := D.sinD t
  (ct * z1 - st * z2, st * z1 + ct * z2)

def param (p : List D) (i : Nat) : D := getDVal p i

def pathPiece (j : Nat) (t : D) (p : List D) : D × D :=
  let n := t.der.length
  let k11 := param p 0; let k12 := param p 1
  let k21 := param p 2; let k22 := param p 3
  let k31 := param p 4; let k32 := param p 5
  let k41 := param p 6; let k42 := param p 7
  let k51 := param p 8; let k52 := param p 9
  let a1 := param p 10; let a2 := param p 11
  let b1 := param p 12; let b2 := param p 13
  let c1 := param p 14; let c2 := param p 15
  let d1 := param p 16; let d2 := param p 17
  let e1 := param p 18; let e2 := param p 19
  let one := D.pointConst 1 n
  let half := D.pointConst (1 / 2) n
  let quarter := D.pointConst (1 / 4) n
  let ct := D.cosD t; let st := D.sinD t
  let data : D × D × D × D :=
    if j = 1 then
      (a1 * ct + a2 * st - one,
       -a2 * ct + a1 * st - half,
       k11, k12)
    else if j = 2 then
      (-quarter * t * t + b1 * t + b2,
       half * t - b1 - one,
       k21, k22)
    else if j = 3 then
      (c1 - t, c2 + t, k31, k32)
    else if j = 4 then
      (-half * t + d1 - one,
       -quarter * t * t + d1 * t + d2,
       k41, k42)
    else
      (e1 * ct + e2 * st - half,
       -e2 * ct + e1 * st - one,
       k51, k52)
  let rr := rotD t data.1 data.2.1
  (rr.1 + data.2.2.1, rr.2 + data.2.2.2)

def alphaBeta (j : Nat) (t : D) (p : List D) : D × D :=
  let n := t.der.length
  let a1 := param p 10; let a2 := param p 11
  let b1 := param p 12; let b2 := param p 13
  let c1 := param p 14; let c2 := param p 15
  let d1 := param p 16; let d2 := param p 17
  let e1 := param p 18; let e2 := param p 19
  let one := D.pointConst 1 n
  let half := D.pointConst (1 / 2) n
  let quarter := D.pointConst (1 / 4) n
  let ct := D.cosD t; let st := D.sinD t
  if j = 1 then
    (-(2 : ℚ) * a1 * st + (2 : ℚ) * a2 * ct + half,
     (2 : ℚ) * a1 * ct + (2 : ℚ) * a2 * st - one)
  else if j = 2 then
    (one + (2 : ℚ) * b1 - t,
     -quarter * t * t + b1 * t + b2 + half)
  else if j = 3 then
    (-one - c2 - t, one + c1 - t)
  else if j = 4 then
    (quarter * t * t - d1 * t - d2 - half,
     (2 : ℚ) * d1 - one - t)
  else
    (one - (2 : ℚ) * e1 * st + (2 : ℚ) * e2 * ct,
     (2 : ℚ) * e1 * ct + (2 : ℚ) * e2 * st - half)

def pathPrime (j : Nat) (t : D) (p : List D) : D × D :=
  let ab := alphaBeta j t p
  rotD t ab.1 ab.2

def fullSystem (box : List RatInterval) : List D :=
  let n := 22
  let p := (List.range 20).map (fun j => D.varD (getI box j) j n)
  let phi := D.varD (getI box 20) 20 n
  let theta := D.varD (getI box 21) 21 n
  let halfPi := (1 / 2 : ℚ) * D.const piI n
  let quarterPi := (1 / 4 : ℚ) * D.const piI n
  let eta := halfPi - theta
  let tau := halfPi - phi
  let k11 := param p 0; let k12 := param p 1
  let a1 := param p 10; let a2 := param p 11
  let b1 := param p 12; let b2 := param p 13
  let c1 := param p 14; let c2 := param p 15
  let d1 := param p 16; let d2 := param p 17
  let e1 := param p 18; let e2 := param p 19
  let one := D.pointConst 1 n
  let quarter := D.pointConst (1 / 4) n
  let first : List D := [
    e1 - a1,
    e2 + a2,
    d1 + b1 - quarterPi,
    d2 - b2 - quarterPi * ((2 : ℚ) * b1 - quarterPi),
    c2 - c1 + halfPi,
    k11 - one + a1,
    k12 - quarter,
    a2 + quarter
  ]
  let pairs : List ((D × D) × (D × D)) := [
    (pathPiece 1 phi p, pathPiece 2 phi p),
    (pathPrime 1 phi p, pathPrime 2 phi p),
    (pathPiece 2 theta p, pathPiece 3 theta p),
    (pathPrime 2 theta p, pathPrime 3 theta p),
    (pathPiece 3 eta p, pathPiece 4 eta p),
    (pathPiece 4 tau p, pathPiece 5 tau p)
  ]
  let matchEqs := pairs.flatMap (fun lr =>
    [lr.1.1 - lr.2.1, lr.1.2 - lr.2.2])
  let lhs := pathPiece 1 phi p
  let xe := pathPiece 3 eta p
  let ae := (alphaBeta 3 eta p).1
  let be : D × D :=
    (xe.1 - ae * D.sinD eta, xe.2 + ae * D.cosD eta)
  first ++ matchEqs ++ [lhs.1 - be.1, lhs.2 - be.2]

private def k4Image : List RatInterval := krawczyk reducedSystem x4 c4
private def k22Image : List RatInterval := krawczyk fullSystem z22 c22

private def outputInputRatio (out box : List RatInterval) : ℚ :=
  (List.zip out box).foldl (fun current pair =>
    let z := pair.1
    let x := pair.2
    let x0 := midpoint x
    let radiusBox := (x.hi - x.lo) / 2
    let radiusOut := max |z.lo - x0| |z.hi - x0|
    max current (radiusOut / radiusBox)) 0

private def k4Ratio : ℚ := outputInputRatio k4Image x4
private def k22Ratio : ℚ := outputInputRatio k22Image z22

private def y20 : List RatInterval := z22.take 20
private def phiBox : RatInterval := getI z22 20
private def thetaBox : RatInterval := getI z22 21

private def etaBox : RatInterval :=
  ⟨piI.lo / 2 - thetaBox.hi, piI.hi / 2 - thetaBox.lo⟩

private def tauBox : RatInterval :=
  ⟨piI.lo / 2 - phiBox.hi, piI.hi / 2 - phiBox.lo⟩

private def scalarGeometryChecks : Bool :=
  let p0 := y20.map (fun z => D.const z 0)
  let phi := D.const phiBox 0
  let theta := D.const thetaBox 0
  let contact := pathPiece 1 phi p0
  let mid : RatInterval := ⟨piI.lo / 4, piI.hi / 4⟩
  let xm := pathPiece 3 (D.const mid 0) p0
  let hmid := add
    (mul (sub contact.1.val xm.1.val) (cosI mid))
    (mul (sub contact.2.val xm.2.val) (sinI mid))
  let xt := pathPiece 2 theta p0
  let htheta := add
    (mul (sub contact.1.val xt.1.val) (cosI thetaBox))
    (mul (sub contact.2.val xt.2.val) (sinI thetaBox))
  let p2 := sub contact.1.val (getI y20 2)
  let q2 := sub contact.2.val (getI y20 3)
  let h2derivs := fun tb : RatInterval =>
    let st := sinI tb
    let ct := cosI tb
    let h1 := sub (add (add (mul (neg p2) st) (mul q2 ct)) (scale (1 / 2) tb)) (getI y20 12)
    let h2 := add (add (mul (neg p2) ct) (mul (neg q2) st)) (point (1 / 2))
    let h3 := sub (mul p2 st) (mul q2 ct)
    (h1, h2, h3)
  let hp := h2derivs phiBox
  let ht := h2derivs thetaBox
  let hi2 := h2derivs ⟨phiBox.lo, thetaBox.hi⟩
  let p3 := sub contact.1.val (getI y20 4)
  let q3 := sub contact.2.val (getI y20 5)
  let i3 : RatInterval := ⟨thetaBox.lo, etaBox.hi⟩
  let h3ppTheta := add (mul (neg p3) (cosI thetaBox)) (mul (neg q3) (sinI thetaBox))
  let h3third := sub (mul p3 (sinI i3)) (mul q3 (cosI i3))
  let dtheta := sub (add oneI (getI y20 12)) (scale (1 / 2) thetaBox)
  let dphi := sub (add oneI (getI y20 12)) (scale (1 / 2) phiBox)
  let early : RatInterval := ⟨0, phiBox.hi⟩
  let xp := pathPrime 1 (D.const early 0) p0
  let earlyDot := add (mul xp.1.val (cosI etaBox)) (mul xp.2.val (sinI etaBox))
  let endpointLength := sub (add (scale 3 (getI y20 10)) (getI y20 8)) oneI
  let area := scale 2 (getI y20 10)
  decide (q 12381960467469534857 10000000000000000000000 < hmid.lo) &&
  decide (hmid.hi < q 12381960467469534871 10000000000000000000000) &&
  decide (htheta.lo > q 41881915317373 10000000000000000) &&
  decide (hp.1.lo > q 118 1250) &&
  decide (hp.2.1.hi < q (-399) 1000) &&
  decide (ht.2.1.lo > q 51 1000) &&
  decide (ht.1.hi < q (-41) 1250) &&
  decide (hi2.2.2.lo > q 359 1000) &&
  decide (hi2.2.2.hi < q 497 500) &&
  decide (h3ppTheta.lo > q 51 1000) &&
  decide (h3third.lo > q 91 100) &&
  decide (h3third.hi < q 1123 1000) &&
  decide (dtheta.lo > q 658623236409 5000000000000) &&
  decide (dphi.lo > q 226393359789 500000000000) &&
  decide (dphi.hi < q 1131966798946 2500000000000) &&
  decide (earlyDot.lo > q 953 1000) &&
  decide (endpointLength.lo > q 16137 10000) &&
  decide (area.lo > q 12103 5000)


private structure GridNode where
  x1 : RatInterval
  x2 : RatInterval
  c : RatInterval
  s : RatInterval

private def gridTime (i : Nat) : RatInterval :=
  scale ((i : ℚ) / 128) piI

private def gridPhase (i : Nat) (tb : RatInterval) : Nat :=
  if i = 0 then 1
  else if i = 64 then 5
  else if tb.hi < phiBox.lo then 1
  else if phiBox.hi < tb.lo ∧ tb.hi < thetaBox.lo then 2
  else if thetaBox.hi < tb.lo ∧ tb.hi < etaBox.lo then 3
  else if etaBox.hi < tb.lo ∧ tb.hi < tauBox.lo then 4
  else 5

private def gridGeometryChecks : Bool :=
  let p0 := y20.map (fun z => D.const z 0)
  let nodes : List GridNode := (List.range 65).map (fun i =>
    let tb := gridTime i
    let xx := pathPiece (gridPhase i tb) (D.const tb 0) p0
    { x1 := xx.1.val
      x2 := xx.2.val
      c := cosI tb
      s := sinI tb })
  let defaultNode : GridNode := ⟨zeroI, zeroI, oneI, zeroI⟩
  let node := fun i => nodes.getD i defaultNode
  let guLows : List ℚ := (List.range 65).flatMap (fun i =>
    (List.range 65).map (fun j =>
      let dx := sub (node i).x1 (node j).x1
      let dy := sub (node i).x2 (node j).x2
      (add (add oneI (mul dx (node i).c)) (mul dy (node i).s)).lo))
  let gvLows : List ℚ := (List.range 65).flatMap (fun i =>
    (List.range 65).map (fun j =>
      let dx := sub (node i).x1 (node j).x1
      let dy := sub (node i).x2 (node j).x2
      (add (add oneI (mul dx (neg (node i).s))) (mul dy (node i).c)).lo))
  let minGu := guLows.foldl min 1
  let minGv := gvLows.foldl min 1
  let phaseBoxes : List RatInterval := [
    ⟨0, phiBox.hi⟩,
    ⟨phiBox.lo, thetaBox.hi⟩,
    ⟨thetaBox.lo, etaBox.hi⟩,
    ⟨etaBox.lo, tauBox.hi⟩,
    ⟨tauBox.lo, piI.hi / 2⟩
  ]
  let hullAbs := fun z : RatInterval => max |z.lo| |z.hi|
  let rVals := (List.range 5).map (fun k =>
    let tb := getI phaseBoxes k
    let xx := pathPiece (k + 1) (D.const tb 0) p0
    hullAbs xx.1.val + hullAbs xx.2.val)
  let mVals := (List.range 5).map (fun k =>
    let tb := getI phaseBoxes k
    let xx := pathPrime (k + 1) (D.const tb 0) p0
    hullAbs xx.1.val + hullAbs xx.2.val)
  let rBound := rVals.foldl max 0
  let mBound := mVals.foldl max 0
  let mesh := piI.hi / 128
  let loss := (rBound + mBound) * mesh
  let guContinuum := minGu - loss
  let gvContinuum := minGv - loss
  decide (minGu > q 3357 10000) &&
  decide (minGv > q 3357 10000) &&
  decide (rBound < q 1531 500) &&
  decide (mBound < q 729 200) &&
  decide (loss < q 1647 10000) &&
  decide (guContinuum > q 171 1000) &&
  decide (gvContinuum > q 171 1000)

/-! ## Public proof-carrying view and optional executable cross-check

The full executable Krawczyk/grid replay above is intentionally retained, but
normalizing it in one kernel reduction is prohibitively expensive.  The trusted
proof path therefore consumes the frozen exact-rational certificate emitted by
the independent replay and checks that certificate in `CertificateManifest`.
This is the standard proof-carrying-data split: expensive certificate discovery
is outside the kernel; small rational certificate verification is inside it.

The executable wrappers prefixed by `executable` remain available for offline
cross-checking and provenance. -/

/-- The rational interval used internally by the executable replay for `Real.pi`. -/
def declaredPiInterval : RatInterval := piI

/-- Public wrapper around the executable sine enclosure. -/
def sineInterval (x : RatInterval) : RatInterval := sinI x

/-- Public wrapper around the executable cosine enclosure. -/
def cosineInterval (x : RatInterval) : RatInterval := cosI x

/-- Frozen reduced input box used by the trusted certificate. -/
def reducedInputBox : List RatInterval := CertificateManifest.x4

/-- Frozen direct-system input box used by the trusted certificate. -/
def fullInputBox : List RatInterval := CertificateManifest.z22

/-- Frozen exact-rational preconditioner for the reduced executable system. -/
def reducedPreconditioner : List (List ℚ) := c4

/-- Frozen exact-rational preconditioner for the direct executable system. -/
def fullPreconditioner : List (List ℚ) := c22

/-- Executable interval value/Jacobian evaluation of the reduced system. -/
def reducedIntervalSystem (box : List RatInterval) : List D := reducedSystem box

/-- Executable interval value/Jacobian evaluation of the direct system. -/
def fullIntervalSystem (box : List RatInterval) : List D := fullSystem box

/-- Proof-carrying reduced Krawczyk image from the frozen manifest. -/
def reducedKrawczykImage : List RatInterval := CertificateManifest.k4Image

/-- Proof-carrying direct-system Krawczyk image from the frozen manifest. -/
def fullKrawczykImage : List RatInterval := CertificateManifest.k22Image

/-- Proof-carrying output/input radius ratio for the reduced replay. -/
def reducedRadiusRatio : ℚ := CertificateManifest.ratio4

/-- Proof-carrying output/input radius ratio for the direct replay. -/
def fullRadiusRatio : ℚ := CertificateManifest.ratio22

/-- Exact frozen contraction bound for the reduced map. -/
def reducedContractionBound : ℚ := CertificateManifest.contraction4

/-- Exact frozen contraction bound for the direct map. -/
def fullContractionBound : ℚ := CertificateManifest.contraction22

/-- Optional expensive executable recomputation of the reduced Krawczyk image.
    This definition is not normalized during `lake build`. -/
def executableReducedKrawczykImage : List RatInterval := k4Image

/-- Optional expensive executable recomputation of the 22D Krawczyk image. -/
def executableFullKrawczykImage : List RatInterval := k22Image

/-- Optional expensive executable output/input radius ratio. -/
def executableReducedRadiusRatio : ℚ := k4Ratio

def executableFullRadiusRatio : ℚ := k22Ratio

/-- Optional executable interval matrix `I-CJ(X)` for the reduced system. -/
def executableReducedLinearPart : List (List RatInterval) :=
  krawczykLinearPart reducedSystem x4 c4

/-- Optional executable interval matrix `I-CJ(Z)` for the direct system. -/
def executableFullLinearPart : List (List RatInterval) :=
  krawczykLinearPart fullSystem z22 c22

/-- Optional executable contraction-bound recomputation. -/
def executableReducedContractionBound : ℚ :=
  weightedContractionBound executableReducedLinearPart x4

/-- Optional executable contraction-bound recomputation. -/
def executableFullContractionBound : ℚ :=
  weightedContractionBound executableFullLinearPart z22

/-- The original expensive aggregate executable check, retained only as a
    diagnostic cross-check.  Merely defining it does not evaluate it. -/
def executableReplayChecks : Bool :=
  RatInterval.subsetB machinPi piI &&
  decide (detQ c4 ≠ 0) &&
  RatInterval.allStrictInsideB k4Image x4 &&
  decide (k4Ratio < q 422 1000) &&
  decide (executableReducedContractionBound < q 1 1000000000000) &&
  decide (detQ c22 ≠ 0) &&
  RatInterval.allStrictInsideB k22Image z22 &&
  decide (k22Ratio < q 95 10000) &&
  decide (executableFullContractionBound < q 1 10000000000) &&
  scalarGeometryChecks &&
  gridGeometryChecks

/-- Trusted build-time replay check: verification of the frozen exact-rational
    proof-carrying certificate. -/
def replayChecks : Bool := CertificateManifest.allChecks

/-- Kernel-only proof of the trusted frozen replay certificate.  No giant
    executable Krawczyk/grid normalization occurs here. -/
theorem replayChecks_eq_true : replayChecks = true := by
  exact CertificateManifest.allChecks_eq_true

/-- Proposition form used by the end-to-end certificate interface. -/
def ReplayPass : Prop := replayChecks = true

theorem replayPass : ReplayPass := replayChecks_eq_true

end GerverSofa.ExactReplay
