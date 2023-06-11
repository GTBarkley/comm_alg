import Mathlib.Order.KrullDimension
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic

def hello : IO Unit := do
  IO.println "Hello, World!"

#eval hello

#check (p q : PrimeSpectrum _) → (p ≤ q)
#check Preorder (PrimeSpectrum _)

#check krullDim (PrimeSpectrum _)