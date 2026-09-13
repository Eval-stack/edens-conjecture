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

& 'C:\Users\zhang\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe' $args
exit $LASTEXITCODE