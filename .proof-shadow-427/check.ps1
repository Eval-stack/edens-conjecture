$paths = @(
  'C:\Users\zhang\OneDrive\Documents\GitHub\edens-conjecture\.proof-shadow-427',
  'C:\Users\zhang\OneDrive\Documents\GitHub\bklps-conjecture\.lake\packages\Cli\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\bklps-conjecture\.lake\packages\batteries\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\bklps-conjecture\.lake\packages\Qq\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\bklps-conjecture\.lake\packages\aesop\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\bklps-conjecture\.lake\packages\proofwidgets\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\bklps-conjecture\.lake\packages\importGraph\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\bklps-conjecture\.lake\packages\LeanSearchClient\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\bklps-conjecture\.lake\packages\plausible\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\bklps-conjecture\.lake\packages\mathlib\.lake\build\lib\lean',
  'C:\Users\zhang\OneDrive\Documents\GitHub\bklps-conjecture\.lake\build\lib\lean',
  'C:\Users\zhang\.elan\toolchains\leanprover--lean4---v4.27.0\lib\lean'
)
$env:LEAN_PATH = $paths -join ';'
& 'C:\Users\zhang\.elan\toolchains\leanprover--lean4---v4.27.0\bin\lean.exe' -R 'C:\Users\zhang\OneDrive\Documents\GitHub\edens-conjecture' 'C:\Users\zhang\OneDrive\Documents\GitHub\edens-conjecture\EdenConjectureProof.lean'
exit $LASTEXITCODE
