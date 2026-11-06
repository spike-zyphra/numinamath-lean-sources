import Mathlib

/- Let  $\alpha,\ \beta$  be the solutions of the quadratic equation  $x^2-3x+5=0$ . Show that for each positive integer  $n$ ,  $\alpha ^ n+\beta ^ n-3^n$  is divisible by 5. -/
theorem number_theory_8930
  (α β : ℂ)
  (hα : α^2 - 3*α + 5 = 0)
  (hβ : β^2 - 3*β + 5 = 0)
  (hαβ : α ≠ β)
  (n : ℕ)
  (hn : n > 0) :
  ∃ z : ℤ, α^n + β^n - 3^n = 5*z := by

  -- We first prove that α + β = 3 and α * β = 5
  apply sub_ne_zero_of_ne at hαβ

  have h₁ : α + β = 3 := by
    -- Subtract the two equations
    have h : (α - β) * (α + β - 3) = (α^2 - 3*α + 5) - (β^2 - 3*β + 5) := by ring
    simp [hα, hβ, hαβ] at h
    exact eq_of_sub_eq_zero h

  have h₂ : α * β = 5 := by
    -- Add the two equations
    have h : α * β = ((α + β)^2 - 3 * (α + β) - (α^2 - 3*α + 5) - (β^2 - 3*β + 5) + 10) / 2 := by ring
    simp [hα, hβ, h₁] at h
    norm_num at h
    exact h

  -- We define the function f(n) = (α^n + β^n - 3^n) / 5
  let f : ℕ → ℂ := λ n => (α^n + β^n - 3^n) / 5

  -- f(1) = 0, f(2) = -2, f(3) = -9 by calculating α^n + β^n when n = 1, 2, 3
  have hf₁ : f 1 = 0 := by
    simp [f, h₁, h₂]

  have hf₂ : f 2 = -2 := by
    simp only [f]
    cancel_denoms
    calc
      α^2 + β^2 - 9 = (α + β)^2 - 2 * (α * β) - 9 := by ring
                  _ = 3^2 - 2 * 5 - 9 := by rw [h₁, h₂]
                  _ = -10 := by norm_num

  have hf₃ : f 3 = -9 := by
    simp only [f]
    cancel_denoms
    calc
      α^3 + β^3 - 27 = (α + β) * ((α + β)^2 - 3 * (α * β)) - 27 := by ring
                  _ = 3 * (3^2 - 3 * 5) - 27 := by rw [h₁, h₂]
                  _ = -45 := by norm_num

  -- Most important observation: f(n + 3) = 6 * f(n + 2) - 14 * f(n + 1) + 15 * f(n)
  -- The characteristic equation of this linear recurrence relation is x^3 - 6x^2 + 14x - 15 = 0
  -- x^3 - 6x^2 + 14x - 15 = (x - 3)(x^2 - 3x + 5)
  -- The roots of this equation are α, β, 3
  have hf n : f (n + 3) = 6 * f (n + 2) - 14 * f (n + 1) + 15 * f n := by
    simp only [f]
    cancel_denoms
    -- Rewrite x^(n + s) as x^n * x^s
    repeat rw [pow_add]
    -- LHS - RHS = (α^3 - 6*α^2 + 14*α - 15) * α^n + (β^3 - 6*β^2 + 14*β - 15) * β^n - (3^3 - 6*3^2 + 14*3 - 15) * 3^n
    -- = 0 * α^n + 0 * β^n - 0 * 3^n = 0
    apply eq_of_sub_eq_zero
    calc α ^ n * α ^ 3 + β ^ n * β ^ 3 - 3 ^ n * 3 ^ 3 - (6 * (α ^ n * α ^ 2 + β ^ n * β ^ 2 - 3 ^ n * 3 ^ 2) - 14 * (α ^ n * α ^ 1 + β ^ n * β ^ 1 - 3 ^ n * 3 ^ 1) + 15 * (α ^ n + β ^ n - 3 ^ n)) = (α^2 - 3*α + 5) * (α - 3) * α^n + (β^2 - 3*β + 5) * (β - 3) * β^n := by ring
         _ = 0 := by simp [hα, hβ, h₁, h₂]

  -- We prove that f(n) is an integer for all n > 0 by defining a recursive helper function h(n) : n > 0 → ∃ z : ℤ, f n = z
  let rec h : ∀ n (_ : n > 0), ∃ z : ℤ, f n = z
    -- n = 0 is impossible
    | 0, h0 => ⟨0, by simp at h0⟩
    -- Three base cases
    | 1, _ => ⟨0, by rw [hf₁]; simp⟩
    | 2, _ => ⟨-2, by rw [hf₂]; simp⟩
    | 3, _ => ⟨-9, by rw [hf₃]; simp⟩
    -- Recursive case
    | n + 4, _ => by
        -- Use the recursive hypothesis
        rcases h (n + 3) (by omega) with ⟨z₃, hz₃⟩
        rcases h (n + 2) (by omega) with ⟨z₂, hz₂⟩
        rcases h (n + 1) (by omega) with ⟨z₁, hz₁⟩
        -- Use hf
        use 6 * z₃ - 14 * z₂ + 15 * z₁
        rw [hf, hz₃, hz₂, hz₁]
        simp

  -- h is almost what we want
  rcases h n hn with ⟨z, hz⟩
  use z
  rw [← hz]
  simp only [f]
  ring
