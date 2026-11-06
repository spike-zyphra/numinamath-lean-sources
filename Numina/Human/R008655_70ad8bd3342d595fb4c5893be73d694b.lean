import Mathlib

/-- All of Marcy's marbles are blue, red, green, or yellow. One third of her marbles are blue, one
fourth of them are red, and six of them are green. What is the smallest number of yellow marbles
that Marcy could have?

$\textbf{(A) }1\qquad\textbf{(B) }2\qquad\textbf{(C) }3\qquad\textbf{(D) }4\qquad\textbf{(E) }5$ -/
theorem number_theory_93334
    (s : Set ℕ) (hs : s = {y : ℕ | ∃ b r g n, n = b + r + g + y ∧ 3 * b = n ∧ 4 * r = n ∧ g = 6}) :
    IsLeast s 4 := by

  -- Let $s$ be the set of all $y$ such that there exist nonnegative integers
  -- $b, r, g, n$ satisfying $n = b + r + g + y$, $3b = n$, $4r = n$, and $g = 6$. Here, $b, r, g, y$
  -- denotes the number of blue, red, green, and yellow balls, respectively. $n$ is the total
  -- number of balls.
  -- We will show that $4$ is the least element of $s$.

  -- First, let's show that $4$ is in $s$.
  have h4s : 4 ∈ s := by
    simp [hs]
    -- Notice that for $n = 24$, $b = 8$, $r = 6$, $g = 4$, and $y = 4$ all conditions are satisfied.
    use 8, 6

  -- Let $y$ be the minimum element of $s$.
  classical let y := Nat.find ⟨4, h4s⟩

  have hys : y ∈ s := by
    classical apply Nat.find_spec ⟨4, h4s⟩

  have hys' := hys
  rw [hs] at hys'
  rcases hys' with ⟨b, r, g, n, hn, hb, hr, rfl⟩

  have hy : IsLeast s y := by
    constructor
    · classical apply Nat.find_spec ⟨4, h4s⟩
    · intro x hx
      classical apply Nat.find_le hx
  have hy' := hy
  obtain ⟨hy1, hy2⟩ := hy'

  -- We will show that $4 \leq y$.
  suffices 4 ≤ y from ?_
  · have : 4 = y := by
      apply le_antisymm this
      apply hy2 h4s
    rw [this]
    exact hy
  clear_value y

  -- First, observe that $n$ must be a multiple 12.
  have : 12 ∣ n := by
    -- To see this, it suffices to show that it is a multiple of $3$ and $4$.
    suffices 3 ∣ n ∧ 4 ∣ n by omega
    split_ands
    -- It is a multiple of $3$ because $3b = n$.
    · use b
      rw [hb]
    -- It is a multiple of $4$ because $4r = n$.
    · use r
      rw [hr]

  -- Write $n = 12 n_0$.
  obtain ⟨n0, rfl⟩ := this

  -- Then, $b = 4 n_0$.
  have : b = 4 * n0 := by linarith only [hb]
  subst this

  -- And, $r = 3 n_0$.
  have : r = 3 * n0 := by linarith only [hr]
  subst this

  -- Substituting these values, we only left with the total number of balls equation: $5 n_0 = 6 + y$.
  have h : 5 * n0 = 6 + y := by linarith only [hn]

  -- Observing this equation, we see that $n_0$ cannot be less than or equal to $1$, so $n_0 \geq 2$.
  -- Because otherwise, $y$ would be negative.
  have : 2 ≤ n0 := by omega

  -- Therefore, $y$ is at least $4$.
  zify  at h this ⊢

  calc (4 : ℤ) = 5 * 2 - 6 := by rfl
       _ ≤ 5 * n0 - 6 := by gcongr
       _ = y := by rw [h]; ring