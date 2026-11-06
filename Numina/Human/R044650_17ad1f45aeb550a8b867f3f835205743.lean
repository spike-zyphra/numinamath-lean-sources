import Mathlib

open Real Polynomial

/- 2. Prove that for every natural number $n, \cos (n x)$ can be expressed as a polynomial in $\cos x$ of degree $n$. -/
theorem algebra_253486 (n : ℕ) :
    ∃ p : Polynomial ℝ, p.degree = n ∧ ∀ x : ℝ, cos (n * x) = p.eval (cos x) := by
  -- The nth Chebyshev polynomial of the first kind satisfies the condition cos (n * x) = p.eval (cos x)
  use Chebyshev.T ℝ n
  simp [Chebyshev.T_real_cos]
  -- It is left to prove that the degree of the Chebyshev polynomial is n.
  -- Proof by induction.
  let rec h : (n : ℕ) → (Chebyshev.T ℝ n).degree = n
  -- If n = 0 then Chebyshev.T 0 = 1.
  | 0 => by simp
  -- If n = 1 then Chebyshev.T 1 = X.
  | 1 => by simp
  | n + 2 => by
    -- Consider n + 2. We need to compute the degree of Chebyshev.T (n + 2) which is equal to
    -- 2 * X * Chebyshev.T (n + 1) - Chebyshev.T n.
    simp only [Nat.cast_add, Nat.cast_ofNat, Polynomial.Chebyshev.T_add_two]
    -- (2 * X).degree = 1.
    have h2 : (2 * X : ℝ[X]).degree = 1 := calc
      (2 * X : ℝ[X]).degree = (C 2 * X : ℝ[X]).degree := by rfl
      _ = 1 := by rw [degree_C_mul_X (by norm_num)]
    -- The degree of Chebyshev.T n = n and the degree of Chebyshev.T (n + 1) = n + 1 (it follows
    -- from the induction hypothesis).
    -- So we get the final result from basic properties of the polynomial degree.
    rw [Polynomial.degree_sub_eq_left_of_degree_lt, Polynomial.degree_mul]
    · rw [show (n : ℤ) + 1 = (n + 1 : ℕ) by simp, h (n + 1), h2]
      norm_cast
      linarith
    rw [h n, Polynomial.degree_mul, h2, show (n : ℤ) + 1 = (n + 1 : ℕ) by simp, h (n + 1)]
    norm_cast
    linarith
  exact h n