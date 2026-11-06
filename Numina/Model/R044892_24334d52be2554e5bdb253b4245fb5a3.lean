import Mathlib

open Nat List

namespace Number_Theory_609174 
/-- Compute the rightmost nonzero digit of n! in base 10. -/
def rightmostNonzeroDigit (n : ℕ) : Option ℕ :=
  let fact := n.factorial
  let digits := digits 10 fact  -- Get decimal digits
  digits.find? (fun d => d ≠ 0) 

end Number_Theory_609174 

open Number_Theory_609174 Option

#eval rightmostNonzeroDigit 10

theorem Number_Theory_609174 {k n: ℕ} (hk : k ≤ 4) (hk' : k ≠ 0) (h : (rightmostNonzeroDigit 101).get! = 2 * k) :
  (((rightmostNonzeroDigit n = rightmostNonzeroDigit 101) ∧ (n ≥ 102)) → n ≥ 103) 
  ∧ ((rightmostNonzeroDigit 103).get! ≡  (rightmostNonzeroDigit 101).get! [ZMOD 10]) := by
  constructor
  · -- First part: If n satisfies the condition and n >= 102, then n >= 103
    intro h1
    by_contra h2
    push_neg at h2
    have h3 : n = 102 := by 
      omega
    rw [h3] at h1
    -- Now $102! = 101! \cdot 102$, so the rightmost nonzero digit changes
    have h4 : rightmostNonzeroDigit 102 ≠ rightmostNonzeroDigit 101 := by 
      native_decide
    have h5 : rightmostNonzeroDigit 102 = rightmostNonzeroDigit 101 := by
      tauto
    contradiction 
  · -- Second part: Show that the rightmost nonzero digit of 103! ≡ rightmost nonzero digit of 101! [MOD 10]
    native_decide