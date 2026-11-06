import Mathlib

/-
Aurélien découpe une feuille de papier en 7 morceaux. Une étape consiste ensuite à choisir un morceau et à le découper en 4,7 ou 10 morceaux. Aurélien peut-il obtenir ainsi 2021 morceaux ?
-/

theorem number_theory_607218 (a : ℕ → ℕ) (ha0 : a 0 = 1) (ha1 : a 1 = 7) (h: ∀n, 2≤ n → (a n = a (n-1) + 4 - 1) ∨ (a n = a (n-1) + 7 - 1) ∨ (a n = a (n-1) + 10 - 1)) : ¬ ∃ k, a k = 2021 := by

    -- for every n, we have a n % 3 = 1, so 2021 is not in the sequence
    have lem : ∀ n:ℕ, (a n) % 3 = 1 := by
        intro n
        induction' n with n hn
        rw [ha0];

        by_cases neq0 : n = 0
        rw [neq0]; simp [ha1];

        have : 2 ≤ n+1 := by omega
        have eq : a (n+1) = a (n + 1 - 1) +4 -1 ∨ a (n+1) = a (n + 1 - 1) + 7 -1 ∨ a (n+1) = a (n +1 - 1) + 10 -1 := by apply h; assumption
        field_simp at eq

        obtain p4 | p7 | p10 := eq
        rw [p4]; simp [hn]
        rw [p7];
        have : a n + 6 = a n + 3 * 2 := by ring_nf
        rw [this]
        have : (a n + 3*2) % 3 = (a n)%3 := by apply Nat.add_mul_mod_self_left
        rw[this]; assumption
        rw [p10]
        have : (a n + 3*3) % 3 = (a n)%3 := by apply Nat.add_mul_mod_self_left
        rw[this]; assumption

    by_contra ek
    obtain ⟨k,hk⟩ := ek
    have akm3: (a k) %3 = 1 := by apply lem
    rw [hk] at akm3; norm_num at akm3
