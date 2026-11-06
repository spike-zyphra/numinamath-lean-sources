import Mathlib

open Real

theorem aime_algebra_715 :
    ∀ p ∈ {(x, y, z) : ℝ × ℝ × ℝ |
          0 < x ∧ 0 < y ∧ 0 < z ∧
          logb 10 (2000*x*y) - (logb 10 x)*(logb 10 y) = 4 ∧
          logb 10 (2*y*z) - (logb 10 y)*(logb 10 z) = 1 ∧
          logb 10 (z*x) - (logb 10 z)*(logb 10 x) = 0},
    ∀ q ∈ {(x, y, z) : ℝ × ℝ × ℝ |
          0 < x ∧ 0 < y ∧ 0 < z ∧
          logb 10 (2000*x*y) - (logb 10 x)*(logb 10 y) = 4 ∧
          logb 10 (2*y*z) - (logb 10 y)*(logb 10 z) = 1 ∧
          logb 10 (z*x) - (logb 10 z)*(logb 10 x) = 0},
    p ≠ q → p.2.1 + q.2.1 = 25 := by

  -- Call the solution set $S$.
  set S := {(x, y, z) : ℝ × ℝ × ℝ |
    0 < x ∧ 0 < y ∧ 0 < z ∧
    logb 10 (2000*x*y) - (logb 10 x)*(logb 10 y) = 4 ∧
    logb 10 (2*y*z) - (logb 10 y)*(logb 10 z) = 1 ∧
    logb 10 (z*x) - (logb 10 z)*(logb 10 x) = 0} with hS

  -- Some helper lemmas. These are just uses the property $\log (a b) = \log a + \log b$.
  have log2000 : logb 10 2000 = logb 10 2 + 3 := by
    calc _ = logb 10 (2 * 10^3) := by congr; norm_num
         _ = logb 10 2 + logb 10 (10^3) := by rw [logb_mul (by norm_num) (by norm_num)]
         _ = logb 10 2 + 3 * logb 10 10 := by rw [logb_pow]; rfl
         _ = logb 10 2 + 3 := by rw [logb_self_eq_one (by norm_num)]; ring
  have log100 : logb 10 100 = 2 := by
    calc _ = logb 10 (10 * 10) := by norm_num
         _ = logb 10 10 + logb 10 10 := by rw [logb_mul (by norm_num) (by norm_num)]
         _ = 1 + 1 := by rw [logb_self_eq_one (by norm_num)]
         _ = 2 := by norm_num
  have log20 : logb 10 20 = logb 10 2 + 1 := by
    calc _ = logb 10 (2 * 10) := by norm_num
         _ = logb 10 2 + logb 10 10 := by rw [logb_mul (by norm_num) (by norm_num)]
         _ = logb 10 2 + 1 := by rw [logb_self_eq_one (by norm_num)]
  have log10' : logb 10 10 = logb 10 5 + logb 10 2 := by
    calc _ = logb 10 (5 * 2) := by norm_num
         _ = logb 10 5 + logb 10 2 := by rw [logb_mul (by norm_num) (by norm_num)]

  -- We will find all the solutions and then prove the theorem easily.
  -- The solutions are $(100, 20, 100)$ and $(1, 5, 1)$.
  have : S = {(100, 20, 100), (1, 5, 1)} := by
    ext ⟨x, y, z⟩
    constructor <;> intro h
    · simp [hS] at h
      rcases h with ⟨hxpos, hypos, hzpos, h1, h2, h3⟩

      -- Simplify the system of equations.
      rw [logb_mul (by nlinarith only [hxpos]) (by nlinarith only [hypos]),
          logb_mul (by norm_num) (by nlinarith only [hxpos]), log2000] at h1
      replace h1 : logb 10 x + logb 10 y - logb 10 x * logb 10 y = 1 - logb 10 2 := by
        linarith only [h1]

      rw [logb_mul (by nlinarith only [hypos]) (by nlinarith only [hzpos]),
          logb_mul (by norm_num) (by nlinarith only [hypos])] at h2
      replace h2 : logb 10 y + logb 10 z - logb 10 y * logb 10 z = 1 - logb 10 2 := by
        linarith only [h2]

      rw [logb_mul (by nlinarith only [hzpos]) (by nlinarith only [hxpos])] at h3

      -- To get rid of the logs, set $a = \log_{10} x$, $b = \log_{10} y$, $c = \log_{10} z$.
      set a := logb 10 x with ha
      set b := logb 10 y with hb
      set c := logb 10 z with hc

      -- Then, factorizing the equations, we get a lot cleaner looking system.
      have h1' : (a - 1) * (b - 1) = logb 10 2 := by nlinarith only [h1]
      have h2' : (b - 1) * (c - 1) = logb 10 2 := by nlinarith only [h2]
      have h3' : (a - 1) * (c - 1) = 1 := by nlinarith only [h3]

      -- Now, we will solve this simpler system instead.
      suffices (a = 2 ∧ b = logb 10 20 ∧ c = 2) ∨ (a = 0 ∧ b = logb 10 5 ∧ c = 0) from ?_
      · rcases this with ⟨ha', hb', hc'⟩ | ⟨ha', hb', hc'⟩
        · left
          simp only [Prod.mk.injEq]
          refine ⟨?_, ?_, ?_⟩
          · apply logb_injOn_pos (b := 10) (by norm_num) hxpos (by norm_num)
            rw [←ha, log100]
            exact ha'
          · apply logb_injOn_pos (b := 10) (by norm_num) hypos (by norm_num)
            rw [←hb]
            exact hb'
          · apply logb_injOn_pos (b := 10) (by norm_num) hzpos (by norm_num)
            rw [←hc, log100]
            exact hc'
        · right
          simp only [Set.mem_singleton_iff, Prod.mk.injEq]
          refine ⟨?_, ?_, ?_⟩
          · apply logb_injOn_pos (b := 10) (by norm_num) hxpos (by norm_num)
            rw [←ha, logb_one]
            exact ha'
          · apply logb_injOn_pos (b := 10) (by norm_num) hypos (by norm_num)
            rw [←hb]
            exact hb'
          · apply logb_injOn_pos (b := 10) (by norm_num) hzpos (by norm_num)
            rw [←hc, logb_one]
            exact hc'

      -- Multiply the equations.
      have h123 : ((a - 1) * (b - 1) * (c - 1))^2 = (logb 10 2)^2 := by
        calc _ = ((a - 1) * (b - 1)) * ((b - 1) * (c - 1)) * ((a - 1) * (c - 1)) := by ring1
             _ = (logb 10 2) * (logb 10 2) * 1 := by rw [h1', h2', h3']
             _ = _ := by ring1
      -- Taking the square root, we have two cases:
      -- $ (a - 1) (b - 1) (c - 1) = \log_{10} 2$ or $ (a - 1) (b - 1) (c - 1) = -\log_{10} 2$.
      replace h123 :
          (a - 1) * (b - 1) * (c - 1) = logb 10 2 ∨
          (a - 1) * (b - 1) * (c - 1) = - logb 10 2 := by
        apply eq_or_eq_neg_of_sq_eq_sq
        exact h123

      rcases h123 with (h123 | h123)
      -- Let's analyse the first case.
      · left; refine ⟨?_, ?_, ?_⟩
        -- Subtitute the value of $(b - 1) (c - 1)$ from the second equation and simplify to find
        -- the value of $a$.
        · rw [mul_assoc, h2'] at h123
          nth_rewrite 2 [←one_mul (logb 10 2)] at h123
          replace h123 := mul_right_cancel₀ (by norm_num) h123
          linarith only [h123]

        -- Substitute the value of $(a - 1) (c - 1)$ from the third equation and simplify to find
        -- the value of $b$.
        · rw [mul_assoc, mul_comm, mul_assoc, mul_comm (c - 1), h3', mul_one] at h123
          rw [log20]
          linarith only [h123]

        -- Substitute the value of $(a - 1) (b - 1)$ from the first equation and simplify to find
        -- the value of $c$.
        · rw [h1'] at h123
          nth_rewrite 2 [←mul_one (logb 10 2)] at h123
          replace h123 := mul_left_cancel₀ (by norm_num) h123
          linarith only [h123]

      -- Let's analyse the second case.
      · right; refine ⟨?_, ?_, ?_⟩
        -- The method is the same. Substitute the value of $(b - 1) (c - 1)$ from the second equation
        -- and simplify to find the value of $a$.
        · rw [mul_assoc, h2', neg_eq_neg_one_mul] at h123
          replace h123 := mul_right_cancel₀ (by norm_num) h123
          linarith only [h123]

        -- Again, substitute the value of $(a - 1) (c - 1)$ from the third equation and simplify to
        -- find the value of $b$.
        · rw [mul_assoc, mul_comm, mul_assoc, mul_comm (c - 1), h3', mul_one,
              ←logb_self_eq_one (b := 10) (by norm_num), log10'] at h123
          linarith only [h123]

        -- Finally, substitute the value of $(a - 1) (b - 1)$ from the first equation and simplify
        -- to find the value of $c$.
        · rw [h1', neg_eq_neg_one_mul, mul_comm (-1)] at h123
          replace h123 := mul_left_cancel₀ (by norm_num) h123
          linarith only [h123]


    · rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      <;> simp [hS]
      · refine ⟨?_, ?_, ?_⟩
        · rw [logb_mul (by norm_num) (by norm_num), logb_mul (by norm_num) (by norm_num),
              log2000, log100, log20]
          ring
        · rw [logb_mul (by norm_num) (by norm_num), logb_mul (by norm_num) (by norm_num),
              log100, log20]
          ring
        · rw [logb_mul (by norm_num) (by norm_num), log100]
          ring
      · refine ⟨?_, ?_⟩
        · rw [logb_mul (by norm_num) (by norm_num), log2000, add_comm, ←add_assoc, ←log10',
              logb_self_eq_one (b := 10) (by norm_num)]
          ring
        · norm_num

  -- Having found all the solutions, the theorem is trivial now.
  simp [this]
  exact ⟨by ring, by ring⟩