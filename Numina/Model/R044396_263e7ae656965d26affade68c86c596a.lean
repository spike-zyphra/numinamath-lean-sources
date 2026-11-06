import Mathlib

open Real Set
open scoped Real

theorem algebra_189280 (x : ℝ) :
  cos (2 * x) + cos (6 * x) + 2 * (sin x) ^ 2 = 1 ↔
  ∃ n : ℤ, x = (π / 12) * (2 * n + 1) := by
  constructor
  · -- Proof for the forward direction: if the equation holds, then x = π/12 (2n+1)
    intro h
    have h1 : cos (2 * x) + cos (6 * x) + 2 * (sin x) ^ 2 = 1 := h
    -- We apply the identity 2 * (sin x) ^ 2 = 1 - cos (2 * x)
    have h2 : 2 * (sin x) ^ 2 = 1 - cos (2 * x) := by
      have h : cos (2 * x) = 1 - 2 * (sin x) ^ 2 := by
        rw [cos_two_mul, sin_sq]
        all_goals ring
      linarith
    -- Substituting into the equation, we get: cos 2x + cos 6x + (1 - cos 2x) = 1, simplifies to cos 6x + 1 = 1, so cos 6x = 0
    rw [h2] at h1
    have h3 : cos (6 * x) = 0 := by
      linarith [h1]
    -- We need to solve cos 6x = 0, which gives 6x = π/2 (2n+1)
    have h4 : ∃ n : ℤ, 6 * x = (Real.pi / 2) * (2 * n + 1) := by
      have h5 : cos (6 * x) = 0 := h3
      obtain ⟨n, hn⟩ := cos_eq_zero_iff.1 h5
      refine ⟨n, ?_⟩
      all_goals
        try { 
          linarith [hn]
        }
        <;> try { 
          nlinarith [hn]
        }
    rcases h4 with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' : x = (Real.pi / 12) * (2 * n + 1) := by
      -- Solving for x
      have h6 : 6 * x = (Real.pi / 2) * (2 * n + 1) := hn
      linarith [h6]
    linarith [hn']
  · -- Proof for the reverse direction: if x = π/12 (2n+1), then the equation holds
    rintro ⟨n, hn⟩
    have h1 : x = (Real.pi / 12) * (2 * n + 1) := by
      linarith [hn]
    -- Calculate 6 * x
    have h2 : 6 * x = (Real.pi / 2) * (2 * n + 1) := by
      have h3 : x = (Real.pi / 12) * (2 * n + 1) := h1
      linarith [h3]
    -- Show that cos(6 * x) = 0
    have h3 : cos (6 * x) = 0 := by
      rw [show 6 * x = (Real.pi / 2) * (2 * n + 1) by linarith [h2]]
      have h5 : cos ((Real.pi / 2) * (2 * n + 1)) = 0 := by
        -- Solving cosine of the real number, gets zero automatically 
        rw [cos_eq_zero_iff]
        use n
        all_goals
          ring_nf <;> norm_num
          <;> linarith
      exact h5
    -- Show the original equation holds
    have h10 : cos (2 * x) + cos (6 * x) + 2 * (sin x) ^ 2 = 1 := by
      have h2 : 2 * (sin x) ^ 2 = 1 - cos (2 * x) := by
        have h : cos (2 * x) = 1 - 2 * (sin x) ^ 2 := by
          rw [cos_two_mul, sin_sq]
          all_goals ring
        linarith
      have h3' : cos (6 * x) = 0 := h3
      nlinarith [h3', h2]
    linarith [h10]