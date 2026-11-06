import Mathlib

theorem algebra_301848 {a : ℕ → ℝ} (ha1 : a 1 = 1) (ha3 : a 3 = 3)
    (hge : ∃ r, ∀ n, a (n + 1) = r * a n) :
    (∑ k in Finset.range 11, Nat.choose 10 k * a (k + 1)) *
    (∑ k in Finset.range 11, (-1 : ℝ)^k * Nat.choose 10 k * a (k + 1)) = 1024 := by
  obtain ⟨r, hr⟩ := hge
  have ha2 : a 2 = r * a 1 := hr 1
  rw [ha1] at ha2
  have ha2' : a 2 = r := by linarith
  have ha3_eq : a 3 = r * a 2 := hr 2
  rw [ha2'] at ha3_eq
  have hr2 : a 3 = r ^ 2 := by linarith
  rw [hr2] at ha3
  have hr2_eq : r^2 = 3 := by nlinarith
  have h1 : ∀ k : ℕ, a (k + 1) = r ^ k := by
    intro k
    induction k with
    | zero =>
      simp [ha1]
    | succ k ih =>
      have h : a (k + 2) = r * a (k + 1) := hr (k + 1)
      rw [show k + 2 = k + 1 + 1 by omega] -- Fix the expression to match the definition
      rw [h]
      rw [ih]
      simp [pow_succ]
      <;> ring_nf <;> linarith
  have h2 : (∑ k in Finset.range 11, Nat.choose 10 k * a (k + 1)) = (1 + r)^10 := by
    simp_rw [h1]
    simp only [Finset.sum_range_succ, Nat.choose]
    norm_num
    <;> ring_nf
    <;> simp [pow_succ] at *
    <;> ring_nf
    <;> linarith
  have h3 : (∑ k in Finset.range 11, (-1 : ℝ)^k * Nat.choose 10 k * a (k + 1)) = (1 - r)^10 := by
    simp_rw [h1]
    simp only [Finset.sum_range_succ, Nat.choose]
    norm_num
    <;> ring_nf
    <;> simp [pow_succ] at *
    <;> ring_nf
    <;> linarith
  rw [h2, h3]
  have hr2 : (1 + r) ^ 10 * (1 - r) ^ 10 = (1 - r^2) ^ 10 := by
    ring_nf
  rw [hr2]
  have h4 : 1 - r^2 = -2 := by nlinarith
  rw [h4]
  norm_num