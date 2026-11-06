import Mathlib

/- 6・3 $f(n)$ is defined on the set of positive integers, and
(1) for any positive integer $n, f(f(n))=4 n+9$;
(2) for any non-negative integer $k, f\left(2^{k}\right)=2^{k+1}+3$. Determine $f(1789)$. -/
theorem algebra_212506 {f : ℕ → ℕ} (fpos : ∀ n, 0<n → 0<f (n)) (hf : ∀ n, 0 < n → f (f n) = 4 * n + 9) (hf' : ∀ k, 0 ≤ k → f (2 ^ k) = 2 ^ (k + 1) + 3) : f 1789 = 3581 := by

  --Iterate the assumption that f(f(n))=4n+9 to get the following lemma.
  have lem : ∀ n, 0<n →  f (4*n + 9) = 4 * f n + 9 := by
    intro n npos
    have eq1: f (f (f n)) = 4 * (f n) + 9 := by 
      apply hf
      apply fpos
      assumption
    have eq2: f (f n) = 4 * n + 9 := by
      apply hf
      assumption
    rw [eq2] at eq1
    assumption

  -- The remaining part is just to calculate f 1789 based on the lemma and the assumptions.
  have f4 : f 4 = 11 := by 
    have : f (2^2) = 2^(2+1) + 3 := by apply hf'; simp
    simp at this; assumption
  have f25: f 25 = 53 := by
    have : f (4*4 +9) = 4 * f 4 + 9 := by apply lem; linarith
    simp [f4] at this; assumption
  have f109 : f 109 = 221 := by
    have : f (4*25+9) = 4*f 25 +9 := by apply lem; linarith
    simp [f25] at this; assumption
  have f445 : f 445 = 893 := by
    have : f (4*109+9) = 4*f 109 + 9 := by apply lem; linarith
    simp [f109] at this; assumption  
  have : f (4*445+9) = 4*f 445 + 9 := by apply lem; linarith
  simp [f445] at this
  assumption