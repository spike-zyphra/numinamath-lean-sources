import Mathlib

theorem algebra_201639 :
    IsLeast {x : ℝ | ∃ α β γ : ℝ, x = abs α + abs β + abs γ ∧ α + β + γ = 2 ∧ α * β * γ = 4} 6 := by
  constructor
  · -- Show 6 is in the set
    use -1, -1, 4
    norm_num [abs]
  · -- Show there is no element less than 6 in the set
    intro x hx
    rcases hx with ⟨α, β, γ, eqx, hsum, hprod⟩
    have h1 : abs α ≥ 0 := abs_nonneg α
    have h2 : abs β ≥ 0 := abs_nonneg β
    have h3 : abs γ ≥ 0 := abs_nonneg γ
    by_cases hα : α ≥ 0
    · -- alpha ≥ 0
      have absα : abs α = α := abs_of_nonneg hα
      by_cases hβ : β ≥ 0
      · -- β ≥ 0
        have absβ : abs β = β := abs_of_nonneg hβ
        by_cases hγ : γ ≥ 0
        · -- γ ≥ 0
          have absγ : abs γ = γ := abs_of_nonneg hγ
          nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (γ - α), 
            mul_nonneg (show 0 ≤ α by linarith) (show 0 ≤ β by linarith), 
            mul_nonneg (show 0 ≤ β by linarith) (show 0 ≤ γ by linarith),
            mul_nonneg (show 0 ≤ α by linarith) (show 0 ≤ γ by linarith)]
        · -- γ < 0
          have absγ : abs γ = -γ := abs_of_neg (show γ < 0 by linarith)
          nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (γ - α), 
            mul_nonneg (show 0 ≤ α by linarith) (show 0 ≤ β by linarith), 
            mul_nonneg (show 0 ≤ β by linarith) (show 0 ≤ -γ by nlinarith),
            mul_nonneg (show 0 ≤ α by linarith) (show 0 ≤ -γ by nlinarith)]
      · -- β < 0
        have absβ : abs β = -β := abs_of_neg (show β < 0 by linarith)
        by_cases hγ : γ ≥ 0
        · -- γ ≥ 0
          have absγ : abs γ = γ := abs_of_nonneg hγ
          nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (γ - α), 
            mul_nonneg (show 0 ≤ α by linarith) (show 0 ≤ -β by nlinarith), 
            mul_nonneg (show 0 ≤ α by linarith) (show 0 ≤ γ by linarith),
            mul_nonneg (show 0 ≤ -β by nlinarith) (show 0 ≤ γ by linarith)]
        · -- γ < 0
          have absγ : abs γ = -γ := abs_of_neg (show γ < 0 by linarith)
          nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (γ - α), 
            mul_nonneg (show 0 ≤ α by linarith) (show 0 ≤ -β by nlinarith), 
            mul_nonneg (show 0 ≤ α by linarith) (show 0 ≤ -γ by nlinarith),
            mul_nonneg (show 0 ≤ -β by nlinarith) (show 0 ≤ -γ by nlinarith)]
    · -- α < 0
      have absα : abs α = -α := abs_of_neg (show α < 0 by linarith)
      by_cases hβ : β ≥ 0
      · -- β ≥ 0
        have absβ : abs β = β := abs_of_nonneg hβ
        by_cases hγ : γ ≥ 0
        · -- γ ≥ 0
          have absγ : abs γ = γ := abs_of_nonneg hγ
          nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (γ - α), 
            mul_nonneg (show 0 ≤ β by linarith) (show 0 ≤ γ by linarith), 
            mul_nonneg (show 0 ≤ -α by nlinarith) (show 0 ≤ β by linarith), 
            mul_nonneg (show 0 ≤ -α by nlinarith) (show 0 ≤ γ by linarith)]
        · -- γ < 0
          have absγ : abs γ = -γ := abs_of_neg (show γ < 0 by linarith)
          nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (γ - α), 
            mul_nonneg (show 0 ≤ β by linarith) (show 0 ≤ -γ by nlinarith), 
            mul_nonneg (show 0 ≤ -α by nlinarith) (show 0 ≤ β by linarith), 
            mul_nonneg (show 0 ≤ -α by nlinarith) (show 0 ≤ -γ by nlinarith)]
      · -- β < 0
        have absβ : abs β = -β := abs_of_neg (show β < 0 by linarith)
        by_cases hγ : γ ≥ 0
        · -- γ ≥ 0
          have absγ : abs γ = γ := abs_of_nonneg hγ
          nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (γ - α), 
              mul_nonneg (show 0 ≤ -α by nlinarith) (show 0 ≤ -β by nlinarith), 
              mul_nonneg (show 0 ≤ -α by nlinarith) (show 0 ≤ γ by linarith), 
              mul_nonneg (show 0 ≤ -β by nlinarith) (show 0 ≤ γ by linarith)]
        · -- γ < 0
          have absγ : abs γ = -γ := abs_of_neg (show γ < 0 by linarith)
          nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (γ - α), 
              mul_nonneg (show 0 ≤ -α by nlinarith) (show 0 ≤ -β by nlinarith), 
              mul_nonneg (show 0 ≤ -α by nlinarith) (show 0 ≤ -γ by nlinarith), 
              mul_nonneg (show 0 ≤ -β by nlinarith) (show 0 ≤ -γ by nlinarith)]