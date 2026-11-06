import Mathlib

theorem algebra_207535 {n : ℕ} (hn : n > 0) (h1 : 3 ∣ n ∧ n % 3 = 16) (h2 : 5 ∣ n ∧ n % 5 = 4) :
    n = 46 := by
        have h3 : 3 ∣ n := h1.1
        have h4 : n % 3 = 16 := h1.2
        have h5 : n % 3 = 0 := by
            exact Nat.dvd_iff_mod_eq_zero.mp h3
        omega -- resolves contradiction