import Mathlib

open Polynomial Complex Real

/- Es sei $n$ eine positive ganze Zahl und $b$ die größte ganze Zahl, die kleiner als $(\sqrt[3]{28}-3)^{-n}$ ist. Man beweise, dass $b$ nicht durch 6 teilbar sein kann. -/
theorem number_theory_604666 (n : ℕ) (hn : 0 < n) :
    ¬ 6 ∣ ⌊((28 : ℝ) ^ (1 / 3 : ℝ) - 3) ^ (- n : ℤ)⌋ := by
  -- The minimal polynomial of [3]√28 - 3 is (X + 3) ^ 3 - 28.
  let p : ℂ[X] := (X + 3) ^ 3 - 28
  -- Set ω := exp(2πi/3), r := [3]√28.
  let ω := exp (2 * π * I / 3)
  -- So ω^2 + ω + 1 = 0 since ω is a primitive 3rd root of unity.
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h := Complex.isPrimitiveRoot_exp 3 (by simp)
    simp at h
    have h₁ := IsPrimitiveRoot.geom_sum_eq_zero h (by simp)
    simpa [Finset.sum, ← add_assoc] using h₁
  -- Also, ω^3 = 1.
  have hω' : ω ^ 3 = 1 := by
    linear_combination hω * (ω - 1)
  -- We know that the real part of ω is -1/2.
  have hω₁ : ω.re = -1 / 2 := by
    norm_num [ω, exp_re, show 2 * π / 3 = π - π / 3 by ring]
  -- Let r := [3]√28.
  let r : ℝ := 28 ^ (1 / 3 : ℝ)
  -- So r^3 = 28.
  have hr : r ^ 3 = 28 := by
    simp [r, ← Real.rpow_mul_natCast]
  -- And r > 0.
  have hr₀ : r > 0 := by
    simp [r]
    positivity
  -- Set α := rω - 3, β := rω^2 - 3, γ := r - 3.
  let α := r * ω - 3
  let β := r * ω ^ 2 - 3
  let γ : ℂ := r - 3
  have hp₀ : p.natDegree = 3 := by
    simp [p]
    compute_degree!
  have hp₁ : p ≠ 0 := by
    intro h
    simp [h] at hp₀
  -- We can compute that α + β + γ = -9, αβ + βγ + γα = 27, αβγ = 1 by algebra.
  have hr₁ : α + β + γ = -9 := by
    simp only [α, β, γ]
    linear_combination r * hω
  have hr₂ : α * β + β * γ + γ * α = 27 := by
    simp only [α, β, γ]
    clear_value r
    ring_nf
    linear_combination (-6 * r + r ^ 2 * ω) * hω
  have hr₃ : α * β * γ = 1 := by
    simp only [α, β, γ]
    clear_value r
    ring_nf
    apply_fun Complex.ofReal at hr
    simp at hr
    rw [hr]
    linear_combination (9 * r - 3 * r ^ 2 * ω) * hω + 28 * hω'
  -- So p = (X - α) * (X - β) * (X - γ).
  have hp : p = (X - C α) * (X - C β) * (X - C γ) := by
    have hr₁' : C α + C β + C γ = -9 := by
      rw [← C_add, ← C_add, hr₁, C_neg]
      rfl
    have hr₂' : C α * C β + C β * C γ + C γ * C α = 27 := by
      rw [← C_mul, ← C_mul, ← C_mul, ← C_add, ← C_add, hr₂]
      rfl
    have hr₃' : C α * C β * C γ = 1 := by
      rw [← C_mul, ← C_mul, hr₃]
      rfl
    simp only [p]
    clear_value α β γ
    linear_combination X ^ 2 * hr₁' - X * hr₂' + hr₃'
  -- So α, β, γ are roots of p.
  have hα : p.eval α = 0 := by
    simp [hp]
  have hβ : p.eval β = 0 := by
    simp [hp]
  have hγ : p.eval γ = 0 := by
    simp [hp]
  simp [p] at hα hβ hγ
  -- So α, β, γ are non-zero.
  have hα₀ : α ≠ 0 := by
    intro hα₀
    norm_num [hα₀] at hα
  have hβ₀ : β ≠ 0 := by
    intro hβ₀
    norm_num [hβ₀] at hβ
  have hγ₀ : γ ≠ 0 := by
    intro hγ₀
    norm_num [hγ₀] at hγ
  -- We know that 1 ≤ ‖α‖, 1 ≤ ‖β‖.
  have hα₁ : 1 ≤ abs α := by
    have h := abs_re_le_abs α
    conv_lhs at h =>
      simp [α, hω₁]
    rw [abs_of_neg (by linarith only [hr₀])] at h
    linarith only [hr₀, h]
  have hβ₁ : 1 ≤ abs β := by
    have h := abs_re_le_abs β
    conv_lhs at h =>
      norm_num [β, show ω ^ 2 = -ω - 1 by linear_combination hω, hω₁]
    rw [abs_of_neg (by linarith only [hr₀])] at h
    linarith only [hr₀, h]
  -- Let's define f(n) := (α ^ n + β ^ n + γ ^ n - 3) / 6 for n ∈ ℤ.
  let f (n : ℤ) : ℂ := (α ^ n + β ^ n + γ ^ n - 3) / 6
  -- We can compute that f(0) = 0, f(1) = -2, f(2) = 4.
  have hf₀ : f 0 = 0 := by
    norm_num [f]
  have hf₁ : f 1 = -2 := by
    norm_num [f, hr₁]
  have hf₂ : f 2 = 4 := by
    calc f 2
      _ = (α ^ (2 : ℤ) + β ^ (2 : ℤ) + γ ^ (2 : ℤ) - 3) / 6 := rfl
      _ = (α ^ 2 + β ^ 2 + γ ^ 2 - 3) / 6 := by norm_cast
      _ = ((α + β + γ) ^ 2 - 2 * (α * β + β * γ + γ * α) - 3) / 6 := by clear_value α β γ; ring
      _ = 4 := by norm_num [hr₁, hr₂]
  -- By the characteristic polynomial of α, β, γ, we know that f(n + 3) + 9 * f(n + 2) + 27 * f(n + 1) - f n = -18.
  have hf (n : ℤ) : f (n + 3) + 9 * f (n + 2) + 27 * f (n + 1) - f n = -18 := by
    simp [f, zpow_add₀ hα₀, zpow_add₀ hβ₀, zpow_add₀ hγ₀]
    clear_value α β γ
    conv_lhs => norm_cast
    linear_combination α ^ n * hα / 6 + β ^ n * hβ / 6 + γ ^ n * hγ / 6
  -- The condition n > 0 is redundant.
  clear hn
  -- f (-n) is an integer.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, f (-n) = k := by
    -- We generalize the hypothesis to f(-n), f(-(n-1)), f(-(n-2)) are integers.
    suffices (∃ k : ℤ, f (-n) = k) ∧ (∃ k : ℤ, f (1-n) = k) ∧ (∃ k : ℤ, f (2-n) = k) from this.1
    -- Let's use induction on n.
    induction n with
    | zero =>
      -- Base case: f(0) = 0, f(1) = -2, f(2) = 4.
      simp [hf₀, hf₁, hf₂]
      exact ⟨⟨0, by simp⟩, ⟨-2, by simp⟩, ⟨4, by simp⟩⟩
    | succ n ih =>
      -- Inductive step: f(-(n+1)) = f(-n) + 9 * f(-(n-1)) + 27 * f(-(n-2)) + 18.
      clear_value f
      push_cast
      specialize hf (-1 - n)
      ring_nf at hf ⊢
      refine ⟨?_, ih.1, ih.2.1⟩
      -- Let's use the induction hypothesis and the recurrence relation.
      obtain ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩, ⟨k₃, hk₃⟩⟩ := ih
      rw [hk₁, hk₂, hk₃] at hf
      use k₃ + 9 * k₂ + 27 * k₁ + 18
      push_cast
      linear_combination -hf
  simp [f] at hk
  -- We know that ‖(α ^ n)⁻¹‖ ≤ 1, ‖(β ^ n)⁻¹‖ ≤ 1.
  have h₁ : ‖(α ^ n)⁻¹‖ ≤ 1 := by
    simp
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ hα₁
  have h₂ : ‖(β ^ n)⁻¹‖ ≤ 1 := by
    simp
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ hβ₁
  -- So ‖(γ ^ n)⁻¹ - 3 - 6 * k‖ ≤ 2 by triangle inequality.
  have h₃ : ‖(γ ^ n)⁻¹ - 3 - 6 * k‖ ≤ 2 := by
    calc ‖(γ ^ n)⁻¹ - 3 - 6 * k‖
      _ = ‖-((α ^ n)⁻¹ + (β ^ n)⁻¹)‖ := by congr; linear_combination hk * 6
      _ = ‖(α ^ n)⁻¹ + (β ^ n)⁻¹‖ := by rw [norm_neg]
      _ ≤ ‖(α ^ n)⁻¹‖ + ‖(β ^ n)⁻¹‖ := norm_add_le _ _
      _ ≤ 2 := by linarith only [h₁, h₂]
  simp [γ, r] at h₃
  -- Convert back to ℝ.
  convert_to Complex.abs ((((28 ^ (3⁻¹ : ℝ)) - 3) ^ n)⁻¹ - 3 - 6 * k : ℝ) ≤ 2 at h₃
  {
    congr
    simp
  }
  rw [abs_ofReal] at h₃
  -- Let's prove by contradiction.
  rintro ⟨k', hk'⟩
  simp at hk'
  -- If 6 ∣ ⌊γ^(-n)⌋, then there is some integer k' such that |γ^(-n) - 6 * k'| < 1.
  have h₄ (a : ℝ) : |a - ⌊a⌋| < 1 := by
    rw [Int.self_sub_floor, abs_lt]
    constructor
    . linarith only [Int.fract_nonneg a]
    . exact Int.fract_lt_one a
  specialize h₄ ((28 ^ (3⁻¹ : ℝ) - 3 : ℝ) ^ n)⁻¹
  simp [hk'] at h₄
  -- So |6 * k + 3 - 6 * k'| < 3.
  have h₅ : |6 * k + 3 - 6 * k'| < 3 := by
    rify
    calc |(6 * k + 3 - 6 * k' : ℝ)|
      _ = |(((28 ^ (3⁻¹ : ℝ) - 3 : ℝ) ^ n)⁻¹ - 6 * k') - (((28 ^ (3⁻¹ : ℝ) - 3 : ℝ) ^ n)⁻¹ - 3 - 6 * k)| := by congr 1; ring
      _ ≤ |((28 ^ (3⁻¹ : ℝ) - 3 : ℝ) ^ n)⁻¹ - 6 * k'| + |((28 ^ (3⁻¹ : ℝ) - 3 : ℝ) ^ n)⁻¹ - 3 - 6 * k| := abs_sub _ _
      _ < 3 := by linarith only [h₃, h₄]
  -- Which is clearly impossible.
  clear * - h₅
  rw [abs_lt] at h₅
  omega
