import Mathlib

theorem algebra_225570 (a b : Fin 1993 → ℝ) (p q : ℝ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (h1 : ∑ i, (a i)^2 = p^2) (h2 : ∑ i, (b i)^2 = q^2) (h3 : ∑ i, a i * b i = p * q) :
    ∃ x, ∀ i, a i / b i = x := by
  use p / q
  intro i
  have h6 : (∑ j : Fin 1993, (a j - p / q * b j) ^ 2) = 0 := by
    have h7 : (∑ j : Fin 1993, (a j - p / q * b j) ^ 2) =
        (∑ j, (a j)^2) - 2 * (p / q) * (∑ j, (a j * b j)) + (p / q) ^ 2 * (∑ j, (b j)^2) := by
      have eq1 : (∑ j : Fin 1993, (a j - p / q * b j) ^ 2) =
          (∑ j : Fin 1993, ((a j)^2 - 2 * (p / q) * (a j * b j) + (p / q) ^ 2 * (b j) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro j _
        ring_nf
      rw [eq1]
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      all_goals ring
    rw [h7]
    rw [h1, h2, h3]
    field_simp [hq]
    all_goals nlinarith
  have h7 : ∀ j : Fin 1993, (a j - p / q * b j) ^ 2 = 0 := by
    intro j
    have h0 : (a j - p / q * b j) ^ 2 ≥ 0 := sq_nonneg (a j - p / q * b j)
    have h00 : (∑ j : Fin 1993, (a j - p / q * b j) ^ 2) = 0 := h6
    have h01 : (a j - p / q * b j) ^ 2 = 0 := by
      have h11 : (a j - p / q * b j) ^ 2 ≥ 0 := sq_nonneg (a j - p / q * b j)
      have h77 : (a j - p / q * b j) ^ 2 ≤ (∑ k : Fin 1993, (a k - p / q * b k) ^ 2) := by
        apply Finset.single_le_sum (fun k _ => sq_nonneg (a k - p / q * b k)) (Finset.mem_univ j)
      rw [show (∑ k : Fin 1993, (a k - p / q * b k) ^ 2) = 0 by linarith] at h77
      linarith
    exact h01
  have h8 : (∀ j : Fin 1993, a j - p / q * b j = 0) := by
    intro j
    have h9 : (a j - p / q * b j) ^ 2 = 0 := h7 j
    have h90 : a j - p / q * b j = 0 := by
      nlinarith
    exact h90
  have h11 : a i * q = p * (b i) := by
    have h12 : a i = p / q * b i := by
      have h20 : a i - p / q * b i = 0 := h8 i
      linarith
    have h13 : b i ≠ 0 := hb i
    have h14 : q ≠ 0 := hq
    field_simp [hb i, hq] at h12 ⊢
    nlinarith [h12]
  have h10 : a i / b i = p / q := by
    have h111 : b i ≠ 0 := hb i
    have h01 : q ≠ 0 := hq
    have eq1 : a i * q = p * (b i) := h11
    have eq2 : ((a i / b i) : ℝ) = p / q := by
      have hbne : (b i) ≠ 0 := hb i
      have hqne : q ≠ 0 := hq
      field_simp [hb i, hq] at eq1 ⊢
      linarith
    exact eq2
  exact h10