import Mathlib


-- Define the maximum possible value of this minimum
theorem Inequalities_607162 {n : ℕ} (hn : n ≥ 1) : (∃ a : ℕ → ℝ, (∀ i, 0 ≤ a i ∧ a i ≤ 1 ∧ a (n + 1) = a 1) ∧ (∀ (i : Fin n), (a i) - a i * a (i + 1) ≥ 1 / (4 : ℝ))) ∧ (∀ (a : ℕ → ℝ), (∀ i, 0 ≤ a i ∧ a i ≤ 1 ∧ a (n + 1) = a 1) → (∃ (i : ℕ), (i ≤ n) ∧ (a i) - a i * a (i + 1) ≤ 1 / (4 : ℝ))) := by
  constructor
  · -- first goal: we can find some $a_i$ such that the minimum equals $\frac{1}{4}$. If all $a_i$ are equal to $\frac{1}{2}$, then all $a_i - a_i a_{i+1}$ are equal to $\frac{1}{4}$, and thus, the minimum is indeed $\frac{1}{4}$.
    let a : ℕ → ℝ := fun _ => (1 / (2 : ℝ))
    use a 
    constructor
    intro i
    constructor
    unfold a
    simp
    constructor
    unfold a
    linarith
    unfold a
    rfl
    intro i
    unfold a
    norm_num
  · -- second goal: -- Let i be such that $a_i$ attains the minimum value. Then we have \( a_{i+1} \geqslant a_i \) (where $a_{n+1} = a_1$), and thus, by the arithmetic-geometric inequality applied to $a_i$ and $1 - a_i$, we obtain $a_i - a_i a_{i+1} \leqslant a_i - a_i^2 = a_i(1 - a_i) \leqslant \frac{1}{4} (a_i + 1 - a_i)^2 = \frac{1}{4}$ Therefore, the minimum of these numbers is at most $\frac{1}{4}$. 
    intro a ha
    -- since `a_1, a_2, …, a_n, a_{n+1} = a_1` has a minimal element.
    have exist_le : ∃ i, (i ≤ n) ∧ a (i + 1) ≥ a i := by 
      by_contra h
      simp at h
      have hc : ∀ (k : ℕ), ((k ≤ n) ∧ k ≥ 1) →  a (k + 1) < a 1 := by
        intro k hk
        induction k with 
        | zero => 
          simp at hk
        | succ t ih => 
          obtain ⟨hk₁, hk₂⟩ := hk
          by_cases h' : t = 0
          rw [h']
          simp
          obtain hone := h 1 (show 1 ≤ n by linarith)
          simp at hone
          exact hone
          have tge : t ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr h'
          have tle : t ≤ n := by linarith
          calc 
            _ < a (t + 1) := by 
              exact h (t + 1) hk₁
            _ < a 1 := by 
              exact ih ⟨tle, tge⟩
      have nlen : n ≤ n := by simp
      obtain hc' := hc n ⟨nlen, hn⟩
      obtain ⟨ha₁, ha₂, ha₃⟩ := ha n
      rw [ha₃] at hc'
      simp at hc'
    obtain ⟨i,hi⟩ := exist_le
    obtain ⟨ile, hi⟩ := hi
    use i
    constructor
    exact ile
    obtain ⟨ha₁, ha₂, ha₃⟩ := ha i
    have goal_ineq : (a i) - a i * a (i + 1) ≤ 1 / (4 : ℝ) := by 
      calc 
        _ ≤ (a i) - (a i) * (a i) := by 
          have ineq_aux : (a i) * (a i) ≤ (a i) * a (i + 1) := by 
            apply mul_le_mul
            simp
            simp [hi, show 0 ≤ (a i) by linarith [ha₁]]
            all_goals { 
              linarith 
            }
          linarith 
        _ = (a i) * (1 - a i) := by ring 
        _ ≤ (1 / (4 : ℝ)) := by
          nlinarith [sq_nonneg ((a i) - 1 / (2 : ℝ))]
    linarith