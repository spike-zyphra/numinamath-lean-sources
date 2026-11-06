import Mathlib

set_option maxRecDepth 5000

theorem algebra_610523 :
    IsLeast { ∑ i : Fin 2023, a i | (a : Fin 2023 → ℤ) (ha : ∀ i, 0 < a i) (h : ∀ k, a k = ∑ i, |a k - a i|)} 2046264 := by
  constructor
  . simp
    let a : Fin 2023 → ℤ := fun i => if i < 1012 then 1011 else 1012
    use a
    native_decide
  . simp [lowerBounds]
    rintro _ a a_k_eq_sum_abs_a_k_sub_a_i a_pos rfl
    wlog monotone_a : Monotone a
    . let σ := Tuple.sort a
      let a' := a ∘ σ
      have monotone_a' : Monotone a' := Tuple.monotone_sort a
      generalize 2023 = n at *
      have sum_a'_ge := by
        apply this a'
        . intro k
          convert a_k_eq_sum_abs_a_k_sub_a_i (σ k) using 1
          . simp [a']
            --generalize a (σ k) = a_σ_k
            exact Fintype.sum_equiv σ (fun i ↦ |a (σ k) - a (σ i)|) (fun i ↦ |a (σ k) - a i|) (congrFun rfl)
        . exact fun i ↦ a_pos (σ i)
        . exact monotone_a'
      have : ∑ i : Fin n, a' i = ∑ i : Fin n, a i := by
        exact Fintype.sum_equiv σ a' a (congrFun rfl)
      rw [this] at sum_a'_ge
      exact sum_a'_ge
    let a_0 := a 0
    set s := ∑ i : Fin 2023, a i
    let n := 2023
    have n_add_1_mul_a_0_eq_s : (n + 1) * a_0 = s := by
      have a_0_eq := a_k_eq_sum_abs_a_k_sub_a_i 0
      have : ∑ i : Fin 2023, |a_0 - a i| = ∑ i : Fin 2023, (a i - a_0) := by
        apply Fintype.sum_congr
        intro i
        suffices a_0 ≤ a i by
          have : a_0 - a i ≤ 0 := by
            linarith
          suffices |a_0 - a i| = - (a_0 - a i) by
            convert this using 1
            ring
          exact abs_of_nonpos this
        have : 0 ≤ i := by
          simp
        exact monotone_a this
      rw [this] at a_0_eq
      rw [Finset.sum_sub_distrib] at a_0_eq
      rw [Finset.sum_const] at a_0_eq
      simp at a_0_eq
      simp [n]
      linarith
    let a_n_sub_1 := a 2022
    have n_sub_1_mul_a_n_sub_1_eq_s : (n - 1) * a_n_sub_1 = s := by
      have a_n_sub_1_eq := a_k_eq_sum_abs_a_k_sub_a_i 2022
      have : ∑ i : Fin 2023, |a_n_sub_1 - a i| = ∑ i : Fin 2023, (a_n_sub_1 - a i) := by
        apply Fintype.sum_congr
        intro i
        suffices a i ≤ a_n_sub_1 by
          have : a_n_sub_1 - a i ≥ 0 := by
            linarith
          exact abs_of_nonneg this
        have : i ≤ 2022 := by
          omega
        exact monotone_a this
      rw [this] at a_n_sub_1_eq
      rw [Finset.sum_sub_distrib] at a_n_sub_1_eq
      rw [Finset.sum_const] at a_n_sub_1_eq
      simp at a_n_sub_1_eq
      simp [n]
      linarith
    simp [n] at n_add_1_mul_a_0_eq_s n_sub_1_mul_a_n_sub_1_eq_s
    have : 1012 * a_0 = 1011 * a_n_sub_1 := by
      linarith
    have : a_0 ≥ 1011 := by
      have := a_pos 0
      omega
    rw [←n_add_1_mul_a_0_eq_s]
    linarith
