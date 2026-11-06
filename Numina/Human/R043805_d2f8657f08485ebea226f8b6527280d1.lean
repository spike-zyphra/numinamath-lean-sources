import Mathlib
open Nat
/-Let $S=M_{13}+5$. Compute the product of all positive divisors of $S$.-/
set_option maxRecDepth 12000 in
theorem Number_Theory_610015 : (mersenne 13 + 5).divisors.prod (fun x => x) = 8196^6 := by
  decide