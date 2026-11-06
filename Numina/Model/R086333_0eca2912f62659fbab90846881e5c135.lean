import Mathlib

theorem algebra_366 : IsGreatest {n : ℕ | IsSquare ((n - 7) * (n + 8))} 56 := by
  constructor
  · -- First, show 56 is in the set
    show IsSquare ((56 - 7) * (56 + 8))
    native_decide

  · -- Now, prove 56 is the greatest
    intro n
    intro hn
    have h : IsSquare ((n - 7) * (n + 8)) := hn

    rcases h with ⟨k, hk⟩

    by_cases h' : n ≥ 7
    · -- Let's suppose n >= 7.

      by_cases h'' : n > 56
      · -- Assume n > 56, derive a contradiction
        have eq2 : n - 7 > 0 := by omega
        have eq3 : n + 8 > 0 := by omega

        have eq1 : (n - 7 : ℕ) * (n + 8 : ℕ) = k * k := by
          linarith [hk]

        have h1 : (n : ℤ) > 56 := by exact_mod_cast h''

        have h2 : (n : ℤ) - 7 > 0 := by omega
        have h3 : (n : ℤ) + 8 > 0 := by omega

        have eq4 : ((n : ℤ) - 7) * ((n : ℤ) + 8) = (k : ℤ) * (k : ℤ) := by
          exact_mod_cast eq1

        have eq5 : ((n : ℤ) - 7) * ((n : ℤ) + 8) = (n : ℤ)^2 + (n : ℤ) - 56 := by
          nlinarith

        have eq6 : (k : ℤ)^2 = (n : ℤ)^2 + (n : ℤ) - 56 := by
          linarith [eq4, eq5]

        have h4 : (k : ℤ) > (n : ℤ) := by
          nlinarith [sq_nonneg ((k : ℤ)), sq_nonneg ((n : ℤ)), eq6]

        have h5 : (k : ℤ) < (n : ℤ) + 1 := by
          nlinarith [sq_nonneg ((k : ℤ)), sq_nonneg ((n : ℤ)), eq6]

        omega

      · -- Now h' => n <= 56
        omega

    · -- Now, suppose n < 7
      have h6 : n < 7 := by omega

      have h7 : n ≤ 56 := by omega

      linarith