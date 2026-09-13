$paths = @(
  'C:\Users\zhang\OneDrive\Documents\GitHub\edens-conjecture',
  'C:\Users\zhang\OneDrive\Documents\GitHub\kourovka-notebook-problem-21.106\.lake\packages\Cli\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\kourovka-notebook-problem-21.106\.lake\packages\batteries\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\kourovka-notebook-problem-21.106\.lake\packages\Qq\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\kourovka-notebook-problem-21.106\.lake\packages\aesop\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\kourovka-notebook-problem-21.106\.lake\packages\proofwidgets\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\kourovka-notebook-problem-21.106\.lake\packages\importGraph\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\kourovka-notebook-problem-21.106\.lake\packages\LeanSearchClient\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\kourovka-notebook-problem-21.106\.lake\packages\plausible\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\kourovka-notebook-problem-21.106\.lake\packages\mathlib\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\kourovka-notebook-problem-21.106\.lake\build\lib\lean',
  'C:\Users\zhang\.elan\toolchains\leanprover--lean4---v4.33.1\lib\lean'
)
$env:LEAN_PATH = $paths -join ';'

$modules = @('EStatementDefinitions', 'EMainProofFlow', 'EMainProofSpectral', 'EMainProofTorus', 'EMainProofSNumbers', 'EMainProofRegularity', 'EMainProofThesis', 'EMainProofVolume', 'EMainProofGlobalSpectrum', 'EMainProofLift', 'EMainProofRefutations', 'EMainProof', 'EStatement', 'EChains')
foreach ($module in $modules) {
  $source = "EdensConjecture/$module.lean"
  $object = "EdensConjecture/$module.olean"
  $newestDependency = [DateTime]::MinValue
  foreach ($match in [regex]::Matches([IO.File]::ReadAllText((Join-Path $pwd $source)), '(?m)^import EdensConjecture\.(\w+)')) {
    $dependency = "EdensConjecture/" + $match.Groups[1].Value + ".olean"
    if (!(Test-Path $dependency)) { throw "Missing compiled dependency: $dependency" }
    $dependencyTime = (Get-Item $dependency).LastWriteTime
    if ($dependencyTime -gt $newestDependency) { $newestDependency = $dependencyTime }
  }
  if (!(Test-Path $object) -or (Get-Item $source).LastWriteTime -gt (Get-Item $object).LastWriteTime -or $newestDependency -gt (Get-Item $object).LastWriteTime) {
    & 'C:\Users\zhang\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe' -o $object $source
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
  }
}
exit 0