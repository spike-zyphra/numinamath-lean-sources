import Mathlib

theorem number_theory_315849 (p : Fin 2015 → ℕ) (hp : ∀ i, Nat.Prime (p i)) (hp1 : ∀ i j, i < j → p i < p j)
    (m : ℕ) (hm : m = ∏ i, p i) :
    ¬∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ (2 * x - y - z) * (2 * y - z - x) * (2 * z - x - y) = m := by
  rintro ⟨x, y, z, hx, hy, hz, heq⟩
  have eq1 : (2 * x - y - z) * (2 * y - z - x) * (2 * z - x - y) = m := heq
  have eq2 : (2 * x - y - z : ℕ) * (2 * y - z - x : ℕ) * (2 * z - x - y : ℕ) = m := by
    norm_cast at eq1 ⊢
  have h2 : (2 * x - y - z : ℕ) > 0 := by
    by_contra h2
    push_neg at h2
    have : (2 * x - y - z : ℕ) = 0 := by
      omega
    rw [this] at eq2
    have : m = 0 := by
      nlinarith
    have hm_pos : m > 0 := by
      rw [hm]
      apply Finset.prod_pos
      intro i hi
      have hi1 : Nat.Prime (p i) := hp i
      have : p i > 0 := by
        exact Nat.Prime.pos hi1
      linarith
    linarith
  have h3 : (2 * y - z - x : ℕ) > 0 := by
    by_contra h3
    push_neg at h3
    have : (2 * y - z - x : ℕ) = 0 := by
      omega
    rw [this] at eq2
    have : m = 0 := by
      nlinarith
    have hm_pos : m > 0 := by
      rw [hm]
      apply Finset.prod_pos
      intro i hi
      have hi1 : Nat.Prime (p i) := hp i
      have : p i > 0 := by
        exact Nat.Prime.pos hi1
      linarith
    linarith
  have h4 : (2 * z - x - y : ℕ) > 0 := by
    by_contra h4
    push_neg at h4
    have : (2 * z - x - y : ℕ) = 0 := by
      omega
    rw [this] at eq2
    have : m = 0 := by
      nlinarith
    have hm_pos : m > 0 := by
      rw [hm]
      apply Finset.prod_pos
      intro i hi
      have hi1 : Nat.Prime (p i) := hp i
      have : p i > 0 := by
        exact Nat.Prime.pos hi1
      linarith
    linarith
  have eq3 : (2 * x - y - z : ℕ) + (2 * y - z - x : ℕ) + (2 * z - x - y : ℕ) = 0 := by
    omega
  nlinarith [h2, h3, h4, eq3]