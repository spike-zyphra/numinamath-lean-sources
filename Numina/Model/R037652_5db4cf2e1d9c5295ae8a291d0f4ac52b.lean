import Mathlib

theorem algebra_189755 (p : ℝ) (hp : 1 ≤ p ∧ p ≤ 2) :
    ∃ f : ℝ → ℝ,
    (∀ x, 2 ≤ x ∧ x < 4 → f x = p) ∧
    (∀ x, f (x + 2) = f x / (5 * f x - 1)) ∧
    f 1985 = p / (5 * p - 1) := by
  use fun x =>
    if (⌊x / 2⌋ : ℤ) % 2 = 0 then p / (5 * p - 1) else p
  constructor
  · -- Verify property (2)
    intro x h
    rcases h with ⟨h1, h2⟩
    have h3 : ⌊x / 2⌋ = 1 := by
      have h6 : 1 ≤ x / 2 := by
        nlinarith
      have h7 : x / 2 < 2 := by
        nlinarith
      have h8 : ⌊x / 2⌋ = 1 := by
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> (try linarith)
      exact h8
    have h9 : (⌊x / 2⌋ : ℤ) % 2 = 1 := by
      omega
    simp [h9]
    all_goals linarith
  constructor
  · -- Show that for all x, f(x+2) = f(x) / (5*f(x) - 1)
    intro x
    have h1 : ⌊(x + 2) / 2⌋ = ⌊x / 2⌋ + 1 := by
      have h3 : ⌊(x + 2) / 2⌋ = ⌊x / 2 + 1⌋ := by
        have h4 : (x + 2) / 2 = x / 2 + 1 := by ring_nf
        rw [h4]
        <;> norm_num [Int.floor_eq_iff]
        <;> linarith
      have h4 : ⌊x / 2 + 1⌋ = ⌊x / 2⌋ + 1 := by
        simp [Int.floor_add_int]
      rw [h3, h4]
    have h6 : (⌊(x + 2) / 2⌋ : ℤ) % 2 = (⌊x / 2⌋ + 1 : ℤ) % 2 := by
      have h7 : ⌊(x + 2) / 2⌋ = ⌊x / 2⌋ + 1 := h1
      rw [h7]
      <;> omega
      <;> try { tauto }
    by_cases h9 : (⌊x / 2⌋ : ℤ) % 2 = 0
    · -- Case where ⌊x/2⌋ is even
      have h10 : (⌊(x + 2) / 2⌋ : ℤ) % 2 = 1 := by 
        omega
      simp [h9, h10] 
      <;> field_simp [(show 5 * p - 1 ≠ 0 by 
        nlinarith [hp.left, hp.right]
      )] <;> ring_nf <;> field_simp [(show 5 * p - 1 ≠ 0 by 
        nlinarith [hp.left, hp.right]
      )] <;> nlinarith
    · -- Case where ⌊x/2⌋ is odd
      have h10 : (⌊(x + 2) / 2⌋ : ℤ) % 2 = 0 := by 
        omega
      simp [h9, h10] 
      <;> field_simp [(show 5 * p - 1 ≠ 0 by 
        nlinarith [hp.left, hp.right]
      )] <;> ring_nf <;> field_simp [(show 5 * p - 1 ≠ 0 by 
        nlinarith [hp.left, hp.right]
      )] <;> nlinarith
  · -- Show that f 1985 = p / (5 * p - 1)
    have h11 : (⌊(1985 : ℝ) / 2⌋ : ℤ) = 992 := by 
      norm_num [Int.floor_eq_iff]
    have h12 : (⌊(1985 : ℝ) / 2⌋ : ℤ) % 2 = 0 := by 
      rw [h11]
      all_goals omega
    simp [h12]
    all_goals linarith
  all_goals try { try { nlinarith } } <;> try { tauto }
  <;> norm_num <;> try { try { nlinarith } } <;> try { tauto }