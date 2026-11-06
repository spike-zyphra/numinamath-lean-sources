import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9088_1 {a : ℝ} (f : ℝ → ℝ) (hf : f = λ x => cos (2 * x) + a * cos x) (ha : a = 2) : IsLeast (range f) (-3/2) := by
  -- first part of the problem. when a=1, minimum value of f(x) is _.
  -- when a=1, we can prove f(x) = 2(cosx+1/2)^2-3/2
  have hf': f = (fun x => 2 * (cos x + 1/2)^2 + (-3/2:ℝ)) := by
    rw [hf, ha]
    funext x
    have: cos (2*x) = 2*(cos x)^2 - 1 := cos_two_mul x
    rw [this]
    ring
  rw [IsLeast]
  -- show f(x) ≤ 1
  have h2: (-3/2:ℝ) ∈ lowerBounds (range f) := by
    rw [lowerBounds]
    simp
    intro x
    rw [hf']
    simp
    have: (cos x + 2⁻¹) ^ 2 ≥ 0 := sq_nonneg (cos x + 2⁻¹)
    have: 0 ≤ 2 * (cos x + 2⁻¹) ^ 2 := by linarith [this]
    linarith [this]
  have h3: (-3/2) ∈ range f := by
    simp
    -- when cosx+1/2 = 0, f(x) reaches minimum.
    -- so use arccos (-1/2) here
    use arccos (-1/2)
    rw [hf']
    simp
    have: cos (arccos (-1 / 2)) = -1/2 := by
      have ht1: -1 ≤ (-1/2:ℝ) := by norm_num
      have ht2: (-1/2:ℝ) ≤ 1 := by norm_num
      apply cos_arccos ht1 ht2
    rw [this]
    ring
  exact ⟨h3, h2⟩

theorem algebra_9088_2 {a : ℝ} (f : ℝ → ℝ) (hf : f = λ x => cos (2 * x) + a * cos x) (hmax: IsGreatest (range f) 2): a = 1 ∨ a = -1 := by
  have hfx : ∀x, f x = 2*(cos x)^2 + a*cos x - 1 := by
    intro x
    rw [hf]
    have h1 : cos (2 * x) = 2*(cos x) ^ 2 - 1 := by
      rw [cos_two_mul]
      <;> ring_nf <;> simp [cos_sq]
      all_goals ring_nf
    simp [h1]
    <;> ring_nf <;> simp [cos_sq]
    all_goals ring_nf
  -- get constraints
  have hx1 : a ≤ 1 := by
    have h1 : f 0 ≤ 2 := by 
      have h1 : f 0 ∈ range f := by 
        use 0 
      apply hmax.2 h1
    have eq2 : f 0 = 1 + a := by
      rw [hfx]
      norm_num 
      <;> ring_nf <;> simp [cos_zero]
      <;> ring 
    nlinarith [eq2, h1]
  have hx3 : a ≥ -1 := by
    have h1 : f Real.pi ≤ 2 := by 
      have h1 : f Real.pi ∈ range f := by 
        use Real.pi 
      apply hmax.2 h1
    have eq2 : f Real.pi = 1 - a := by
      rw [hfx]
      have hcos : cos Real.pi = -1 := by 
        rw [cos_pi]
      rw [hcos]
      norm_num 
      <;> ring_nf <;> simp [cos_zero]
      <;> ring 
    nlinarith [eq2, h1]
  have h2eq : 2 ∈ range f := hmax.1
  rcases h2eq with ⟨x, hx⟩
  have eq2 : f x = 2 := by
    simpa using hx
  have eq1 : 2*(cos x) ^2 + a*cos x - 1 = 2 := by
    have eq3 : f x = 2 := eq2 
    rw [hfx] at eq3 
    linarith 
  have h11 : -1 ≤ cos x ∧ cos x ≤ 1 := by 
    constructor 
    · linarith [neg_one_le_cos x]
    · linarith [cos_le_one x]
  have eq3 : (a - 1) * (a + 1) = 0 := by
    nlinarith [sq_nonneg (cos x - (1)), sq_nonneg (cos x + (1)), sq_nonneg (a - 1), sq_nonneg (a + 1), h11.1, h11.2, sq_nonneg (cos x ^2), sq_nonneg (a ^ 2)]
  cases' (mul_eq_zero.mp eq3) with ha1 ha2
  · left
    linarith 
  · right
    linarith