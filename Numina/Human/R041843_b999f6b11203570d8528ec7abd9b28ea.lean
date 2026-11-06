import Mathlib

/- The difference between two perfect squares is 133.  What is the smallest possible sum of the two perfect squares? -/
theorem algebra_10439 : IsLeast {n : ℕ | ∃ a, ∃ b, (a ^ 2 - b ^ 2 = 133 ∧ n = a ^ 2 + b ^ 2)} 205 := by
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  -- Prove that there exists a and b such that their sum of squares is minimized.
  use 13, 6
  norm_num
  -- Prove that 205 is indeed a lower bound of the sum of squares of a and b.
  intro n a b g₀ g₁
  rw [Nat.sq_sub_sq] at g₀
  -- We have (a + b) * (a - b) = 133.
  let x : ℕ × ℕ := (a + b, a - b)
  have hx : x.1 * x.2 = 133 ∧ 133 ≠ 0 := by
    refine ⟨?_, ?_⟩
    simpa
    norm_num
  rw [<-Nat.mem_divisorsAntidiagonal] at hx
  -- Use the computer to find the factors of 133 (native_decide is necessary).
  rw [show Nat.divisorsAntidiagonal 133 = {(1, 133), (7, 19), (19, 7), (133, 1)} by native_decide] at hx
  simp at hx
  obtain hx | hx | hx | hx := hx
  . -- The case (a + b, a - b) = (1, 133). Impossible.
    have h₀ : a + b = 1 := by
      calc
        a + b = x.1 := by simp
        _ = 1 := by rw [hx]
    have h₁ : a - b = 133 := by
      calc
        a - b = x.2 := by simp
        _ = 133 := by rw [hx]
    -- A contradiction is derived.
    omega
  . -- The case (a + b, a - b) = (7, 19). Impossible.
    have h₀ : a + b = 7 := by
      calc
        a + b = x.1 := by simp
        _ = 7 := by rw [hx]
    have h₁ : a - b = 19 := by
      calc
        a - b = x.2 := by simp
        _ = 19 := by rw [hx]
    -- A contradiction is derived.
    omega
  . -- The case (a + b, a - b) = (19, 7).
    have h₀ : a + b = 19 := by
      calc
        a + b = x.1 := by simp
        _ = 19 := by rw [hx]
    have h₁ : a - b = 7 := by
      calc
        a - b = x.2 := by simp
        _ = 7 := by rw [hx]
    have h₂ : a = 13 := by
      calc
        a = a * 2 / 2 := by simp
        _ = (a + b + (a - b)) / 2 := by omega
        _ = (19 + 7) / 2 := by rw [h₀, h₁]
        _ = 13 := by norm_num
    have h₃ : b = 6 := by
      omega
    rw [g₁, h₂, h₃]
    omega
  . -- The case (a + b, a - b) = (133, 1).
    have h₀ : a + b = 133 := by
      calc
        a + b = x.1 := by simp
        _ = 133 := by rw [hx]
    have h₁ : a - b = 1 := by
      calc
        a - b = x.2 := by simp
        _ = 1 := by rw [hx]
    have h₂ : a = 67 := by
      calc
        a = a * 2 / 2 := by simp
        _ = (a + b + (a - b)) / 2 := by omega
        _ = (133 + 1) / 2 := by rw [h₀, h₁]
        _ = 67 := by norm_num
    have h₃ : b = 66 := by
      omega
    rw [g₁, h₂, h₃]
    omega
