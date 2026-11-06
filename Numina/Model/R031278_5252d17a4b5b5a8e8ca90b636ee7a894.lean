import Mathlib

theorem number_theory_292952 (u : ℕ → ℤ) (h : Function.Periodic u 2022) (h' : Function.Periodic u 5) :
    ∃ c, ∀ n, u n = c := by 
  have h1 : ∀ n, u (n + 2022) = u n := by
    intro n
    exact h n

  have h2 : ∀ n, u (n + 5) = u n := by
    intro n
    exact h' n
  -- Show that $u_{n+1} = u_n$.
  have h3 : ∀ n, u (n + 1) = u n := by
    intro n
    have h4 : ∀ (k : ℕ), u (n + k * 5) = u n := by
      intro k
      induction k with
      | zero => 
        simp
      | succ k ih =>
        calc
          u (n + (k + 1) * 5) = u ( (n + k * 5) + 5 ) := by ring_nf
          _ = u (n + k * 5) := by apply h2
          _ = u n := by exact ih
    have h6 : u (n + 809 * 5) = u n := by
      specialize h4 809
      simpa using h4
    -- Show $u_{n+1 + 2*2022} = u_{n+1}$.
    have h7 : u (n + 1 + 2 * 2022) = u (n + 1) := by
      have eq1 : u (n + 1 + 2022) = u (n + 1) := by
        apply h1
      have eq2 : u (n + 1 + 2 * 2022) = u (n + 1 + 2022) := by
        have eq3 : u ((n + 1 + 2022) + 2022) = u (n + 1 + 2022) := by
          apply h1
        have eq4 : (n + 1 + 2 * 2022) = (n + 1 + 2022) + 2022 := by 
          omega 
        rw [eq4]
        linarith [eq3]
      linarith [eq1, eq2]
    -- Show the relationship between $n + 809 \cdot 5$ and $n + 1 + 2 \cdot 2022$.
    have h8 : n + 809 * 5 = n + 1 + 2 * 2022 := by 
      omega
    -- Now prove equality of $h6$ and $h7$.
    rw [h8] at h6
    linarith [h6, h7]

  -- Since for all $n$, $u_{n+1} = u_n$, the sequence is constant.
  use u 0
  intro n
  induction n with
  | zero => 
    all_goals 
      simp
  | succ n ih =>
    have h11 : u (n + 1) = u n := h3 n
    have h12 : u (n + 1) = u 0 := by 
      linarith [ih, h11]
    linarith [h12]