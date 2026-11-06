import Mathlib

def s : Set ℕ := {n | ¬∃ x y, n = 5*x + 7*y}

theorem number_theory_343 : IsGreatest s 23 := by
  constructor
  · -- First, show 23 ∈ s
    show 23 ∈ s
    unfold s
    intro h
    rcases h with ⟨x, y, h⟩
    have h1 : x ≤ 4 := by
      omega
    have h2 : y ≤ 3 := by
      omega
    interval_cases x <;> interval_cases y <;> omega
  · -- Now, show that for any n ∈ s, n ≤ 23
    intro n hn
    have h : n ∈ s := hn
    unfold s at h
    by_contra h'
    push_neg at h'
    have h3 : ∃ x y, n = 5 * x + 7 * y := by
      have h4 : n ≥ 24 := by omega
      have : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by 
        omega
      rcases this with (h | h | h | h | h)
      · -- Case n % 5 = 0
        use n / 5, 0
        omega
      · -- Case n % 5 = 1
        use (n - 21) / 5, 3
        omega
      · -- Case n % 5 = 2
        use (n - 7) / 5, 1
        omega
      · -- Case n % 5 = 3
        use (n - 28) / 5, 4
        omega
      · -- Case n % 5 = 4
        use (n - 14) / 5, 2
        omega
    contradiction