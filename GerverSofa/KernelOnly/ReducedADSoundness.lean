import GerverSofa.KernelOnly.ADCoreSoundness

/-!
# Concrete interval-AD soundness for the reduced 4D system

This module instantiates the constructor-level AD theorem with equations
(F1)--(F4), proves that the frozen rational list is exactly the manuscript box,
and identifies the four smooth scalar models with `Reduced.vectorSystem`.
-/

noncomputable section

namespace GerverSofa

open RatInterval

namespace Reduced

/-- The four frozen rational intervals are exactly the named reduced box. -/
theorem inputBox_exact (x : Vec 4) :
    x ∈ vectorBox ↔ EnclosesVec ExactReplay.reducedInputBox x := by
  constructor
  · intro hx
    change coordEquiv.symm x ∈ box at hx
    dsimp [box, qR, coordEquiv] at hx
    refine ⟨?_, ?_⟩
    · norm_num [ExactReplay.reducedInputBox, CertificateManifest.x4]
    · intro i
      fin_cases i <;>
        simp [ExactReplay.reducedInputBox, CertificateManifest.x4,
          CertificateManifest.q, ExactReplay.getI, RatInterval.Contains] <;>
        aesop
  · rintro ⟨hlen, hx⟩
    change coordEquiv.symm x ∈ box
    dsimp [box, qR, coordEquiv]
    have h0 := hx (0 : Fin 4)
    have h1 := hx (1 : Fin 4)
    have h2 := hx (2 : Fin 4)
    have h3 := hx (3 : Fin 4)
    simp [ExactReplay.reducedInputBox, CertificateManifest.x4,
      CertificateManifest.q, RatInterval.Contains] at h0 h1 h2 h3
    aesop

/-- Both angular coordinates of the reduced box lie in the physical quadrant. -/
theorem reduced_angles_physical {x : Vec 4} (hx : x ∈ vectorBox) :
    (0 ≤ x 2 ∧ x 2 ≤ Real.pi / 2) ∧
    (0 ≤ x 3 ∧ x 3 ≤ Real.pi / 2) := by
  have henc := (inputBox_exact x).1 hx
  have hphi := henc.2 (2 : Fin 4)
  have htheta := henc.2 (3 : Fin 4)
  simp [ExactReplay.reducedInputBox, CertificateManifest.x4,
    CertificateManifest.q, RatInterval.Contains] at hphi htheta
  constructor <;> constructor <;>
    nlinarith [Real.pi_gt_three]

/-- Scalar models matching the four reduced equations. -/
def models : Fin 4 → ScalarModel 4 :=
  let a := ScalarModel.var 4 (0 : Fin 4)
  let b := ScalarModel.var 4 (1 : Fin 4)
  let phi := ScalarModel.var 4 (2 : Fin 4)
  let theta := ScalarModel.var 4 (3 : Fin 4)
  let one := ScalarModel.const 4 1
  let half := ScalarModel.const 4 (1 / 2 : ℝ)
  let quarter := ScalarModel.const 4 (1 / 4 : ℝ)
  let piM := ScalarModel.const 4 Real.pi
  let cp := ScalarModel.cos phi
  let sp := ScalarModel.sin phi
  let ct := ScalarModel.cos theta
  let st := ScalarModel.sin theta
  let delta := theta - phi
  let f1 := a * (ct - cp) - (2 : ℚ) * b * sp + (delta - one) * ct - st + cp + sp
  let f2 := a * ((3 : ℚ) * st + sp) - (2 : ℚ) * b * cp
    + (3 : ℚ) * (delta - one) * st + (3 : ℚ) * ct - sp + cp
  let f3 := a * cp - sp - half + half * cp - b * sp
  let f4 := a + (1 / 2 : ℚ) * piM - phi - theta - b
    + half * delta * (one + a) + quarter * delta * delta
  ![f1, f2, f3, f4]

/-- The model values are definitionally the manuscript reduced system after
coordinate conversion. -/
theorem vectorSystem_eq_models (x : Vec 4) :
    vectorSystem x = fun i => (models i).value x := by
  funext i
  fin_cases i <;>
    simp [vectorSystem, coordEquiv, system, models, ScalarModel.var,
      ScalarModel.const, ScalarModel.add, ScalarModel.neg, ScalarModel.sub,
      ScalarModel.mul, ScalarModel.scale, ScalarModel.sin, ScalarModel.cos] <;>
    ring

/-- Every executable output dual interval is sound for its corresponding
reduced scalar model. -/
theorem output_models_sound (i : Fin 4) :
    DSoundOn vectorBox
      ((ExactReplay.reducedIntervalSystem ExactReplay.reducedInputBox).getD i.1
        (ExactReplay.D.const ExactReplay.zeroI 4))
      (models i) := by
  let input := ExactReplay.reducedInputBox
  let X := vectorBox
  let da := ExactReplay.D.varD (ExactReplay.getI input 0) 0 4
  let db := ExactReplay.D.varD (ExactReplay.getI input 1) 1 4
  let dphi := ExactReplay.D.varD (ExactReplay.getI input 2) 2 4
  let dtheta := ExactReplay.D.varD (ExactReplay.getI input 3) 3 4
  let done := ExactReplay.D.pointConst 1 4
  let dhalf := ExactReplay.D.pointConst (1 / 2) 4
  let dquarter := ExactReplay.D.pointConst (1 / 4) 4
  let dpi := ExactReplay.D.const ExactReplay.piI 4
  let dcp := ExactReplay.D.cosD dphi
  let dsp := ExactReplay.D.sinD dphi
  let dct := ExactReplay.D.cosD dtheta
  let dst := ExactReplay.D.sinD dtheta
  let ddelta := dtheta - dphi

  let ma := ScalarModel.var 4 (0 : Fin 4)
  let mb := ScalarModel.var 4 (1 : Fin 4)
  let mphi := ScalarModel.var 4 (2 : Fin 4)
  let mtheta := ScalarModel.var 4 (3 : Fin 4)
  let mone := ScalarModel.const 4 1
  let mhalf := ScalarModel.const 4 (1 / 2 : ℝ)
  let mquarter := ScalarModel.const 4 (1 / 4 : ℝ)
  let mpi := ScalarModel.const 4 Real.pi

  have hvar (k : Fin 4) : ∀ x ∈ X,
      Contains (ExactReplay.getI input k.1) (x k) := by
    intro x hx
    exact ((inputBox_exact x).1 hx).2 k
  have ha : DSoundOn X da ma := by
    simpa [da, ma] using DSoundOn.varD (X := X)
      (ExactReplay.getI input 0) (0 : Fin 4) (hvar 0)
  have hb : DSoundOn X db mb := by
    simpa [db, mb] using DSoundOn.varD (X := X)
      (ExactReplay.getI input 1) (1 : Fin 4) (hvar 1)
  have hphi : DSoundOn X dphi mphi := by
    simpa [dphi, mphi] using DSoundOn.varD (X := X)
      (ExactReplay.getI input 2) (2 : Fin 4) (hvar 2)
  have htheta : DSoundOn X dtheta mtheta := by
    simpa [dtheta, mtheta] using DSoundOn.varD (X := X)
      (ExactReplay.getI input 3) (3 : Fin 4) (hvar 3)
  have hone : DSoundOn X done mone := by
    simpa [done, mone] using DSoundOn.pointConst (X := X) (n := 4) (1 : ℚ)
  have hhalf : DSoundOn X dhalf mhalf := by
    simpa [dhalf, mhalf] using DSoundOn.pointConst (X := X) (n := 4) (1 / 2 : ℚ)
  have hquarter : DSoundOn X dquarter mquarter := by
    simpa [dquarter, mquarter] using DSoundOn.pointConst (X := X) (n := 4) (1 / 4 : ℚ)
  have hpi : DSoundOn X dpi mpi := by
    simpa [dpi, mpi] using DSoundOn.const (X := X) ExactReplay.piI_contains_pi

  have hphiPhys : ∀ x ∈ X,
      0 ≤ mphi.value x ∧ mphi.value x ≤ Real.pi / 2 := by
    intro x hx
    simpa [mphi, ScalarModel.var] using (reduced_angles_physical hx).1
  have hthetaPhys : ∀ x ∈ X,
      0 ≤ mtheta.value x ∧ mtheta.value x ≤ Real.pi / 2 := by
    intro x hx
    simpa [mtheta, ScalarModel.var] using (reduced_angles_physical hx).2
  have hcp := hphi.cos hphiPhys
  have hsp := hphi.sin hphiPhys
  have hct := htheta.cos hthetaPhys
  have hst := htheta.sin hthetaPhys
  have hdelta := htheta.sub hphi

  /- Preserve the exact left-associated AST used by `reducedSystem` and
     `models`.  In particular `q * u * v` is `(q * u) * v`, not
     `q * (u * v)`. -/
  have hf1 := (((((ha.mul (hct.sub hcp)).sub
      ((DSoundOn.scale (2 : ℚ) hb).mul hsp)).add
      ((hdelta.sub hone).mul hct)).sub hst).add hcp).add hsp
  have hf2 := (((((ha.mul ((DSoundOn.scale (3 : ℚ) hst).add hsp)).sub
      ((DSoundOn.scale (2 : ℚ) hb).mul hcp)).add
      ((DSoundOn.scale (3 : ℚ) (hdelta.sub hone)).mul hst)).add
      (DSoundOn.scale (3 : ℚ) hct)).sub hsp).add hcp
  have hf3 := ((((ha.mul hcp).sub hsp).sub hhalf).add
      (hhalf.mul hcp)).sub (hb.mul hsp)
  have hf4 := (((((ha.add (DSoundOn.scale (1 / 2 : ℚ) hpi)).sub hphi).sub
      htheta).sub hb).add
      ((hhalf.mul hdelta).mul (hone.add ha))).add
      ((hquarter.mul hdelta).mul hdelta)

  fin_cases i
  · simpa [ExactReplay.reducedIntervalSystem, ExactReplay.reducedSystem,
      input, X, da, db, dphi, dtheta, done, dhalf, dquarter, dpi, dcp, dsp,
      dct, dst, ddelta, models, ma, mb, mphi, mtheta, mone, mhalf,
      mquarter, mpi] using hf1
  · simpa [ExactReplay.reducedIntervalSystem, ExactReplay.reducedSystem,
      input, X, da, db, dphi, dtheta, done, dhalf, dquarter, dpi, dcp, dsp,
      dct, dst, ddelta, models, ma, mb, mphi, mtheta, mone, mhalf,
      mquarter, mpi] using hf2
  · simpa [ExactReplay.reducedIntervalSystem, ExactReplay.reducedSystem,
      input, X, da, db, dphi, dtheta, done, dhalf, dquarter, dpi, dcp, dsp,
      dct, dst, ddelta, models, ma, mb, mphi, mtheta, mone, mhalf,
      mquarter, mpi] using hf3
  · simpa [ExactReplay.reducedIntervalSystem, ExactReplay.reducedSystem,
      input, X, da, db, dphi, dtheta, done, dhalf, dquarter, dpi, dcp, dsp,
      dct, dst, ddelta, models, ma, mb, mphi, mtheta, mone, mhalf,
      mquarter, mpi] using hf4

/-- Concrete semantic correctness of the complete reduced interval-AD call. -/
def reducedADSoundness : ADSystemSoundness
    vectorSystem vectorBox ExactReplay.reducedInputBox
      ExactReplay.reducedIntervalSystem where
  input_exact := inputBox_exact
  output_sound := by
    intro x hx
    apply adOutputSoundAt_of_models
      (X := vectorBox)
      (out := ExactReplay.reducedIntervalSystem ExactReplay.reducedInputBox)
      (models := models)
      (F := vectorSystem)
    · norm_num [ExactReplay.reducedIntervalSystem, ExactReplay.reducedSystem]
    · exact output_models_sound
    · exact vectorSystem_eq_models
    · exact hx

end Reduced

end GerverSofa
