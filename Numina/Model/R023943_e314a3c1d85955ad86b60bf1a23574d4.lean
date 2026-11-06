import Mathlib

theorem algebra_141863 {n : ℕ} (hn : n ≤ 3) :
    ∃ p : Polynomial ℝ, p.degree = n ∧ ∀ k ∈ Finset.range (n + 1), p.coeff k = 1 ∨ p.coeff k = -1 ∧
      ∀ x ∈ p.roots, ∃ r : ℝ, x = r := by
  have h1 : n ≤ 3 := hn
  have h2 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
    omega
  rcases h2 with (rfl | rfl | rfl | rfl)
  · -- n=0, p=1
    use Polynomial.C (1 : ℝ)
    constructor
    · -- compute degree
      compute_degree!
      <;> simp
      <;> norm_num
      <;> try { native_decide }
    · -- verify coefficients are ±1 and real roots condition
      intro k hk
      fin_cases hk <;> simp [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_C, Finset.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      <;> norm_num
      <;> try { native_decide }
      <;> try { native_decide }
  · -- n=1, p=X+1
    use Polynomial.X + Polynomial.C (1 : ℝ)
    constructor
    · -- compute degree
      compute_degree!
      <;> simp
      <;> norm_num
      <;> try { native_decide }
    · -- verify coefficients are ±1 and real roots condition
      intro k hk
      fin_cases hk <;> simp [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C, Finset.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      <;> norm_num
      <;> try { native_decide }
      <;> try { native_decide }
  · -- n=2, p=X^2+X+1
    use Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (1 : ℝ)
    constructor
    · -- compute degree
      compute_degree!
      <;> simp
      <;> norm_num
      <;> try { native_decide }
    · -- verify coefficients are ±1 and real roots condition
      intro k hk
      fin_cases hk <;> simp [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Finset.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      <;> norm_num
      <;> try { native_decide }
      <;> try { native_decide }
  · -- n=3, p=X^3+X^2+X+1
    use Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (1 : ℝ)
    constructor
    · -- compute degree
      compute_degree!
      <;> simp
      <;> norm_num
      <;> try { native_decide }
    · -- verify coefficients are ±1 and real roots condition
      intro k hk
      fin_cases hk <;> simp [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Finset.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      <;> norm_num
      <;> try { native_decide }
      <;> try { native_decide }