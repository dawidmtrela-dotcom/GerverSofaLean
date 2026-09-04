$ErrorActionPreference = "Stop"
lake build GerverSofa.KernelOnly.PartE.E24KC6KernelFinalAxiomAudit
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
Write-Host "REPRODUCTION PASS" -ForegroundColor Green