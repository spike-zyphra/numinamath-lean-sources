import Mathlib

/- Déterminer tous les entiers $n \geqslant 0$ tels que $2023+n$ ! est un carré parfait. -/
theorem number_theory_607176 (n : ℕ) :
    IsSquare (2023 + (Nat.factorial n)) ↔ n = 2 := by 
    constructor
    · intro h
      --Soit $n \geqslant 0$ tel que $2023+n$ ! est un carré parfait.
      by_cases hn : n ≥ 4
      · --Si $n \geqslant 4$,
        obtain ⟨r, hr⟩ := h
        --alors 4 divise $n$ !,
        have h1 : 4 ∣ Nat.factorial n := by
          apply Nat.dvd_factorial
          linarith
          exact hn
        have h2 : Nat.factorial n % 4 = 0 := by
          exact Nat.dvd_iff_mod_eq_zero.mp h1
        have h3 : 2023 % 4 = 3 := by norm_num
        --donc $2023+\mathrm{n}!\equiv 2023 \equiv 3(\bmod 4)$.
        have h4 : (2023 + Nat.factorial n) % 4 = 3 := by
          rw [Nat.add_mod, h2, h3]
        --Or 3 n'est pas un carré modulo 4 (les carrés modulo 4 sont 0 et 1 ),
        have h5 : (r * r) % 4 ≠ 3 := by 
          have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
          rcases this with (h | h | h | h) <;>
          simp [h, pow_two, Nat.mul_mod, Nat.add_mod]
        --donc on a une contradiction.
        omega
      · --Ainsi $n \leqslant 3$.
        by_contra! hn'
        have h1 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
        cases' h1 with h2 h3
        --Notons que $44^{2}=1936&lt;2023+0!=2023+1!=2024&lt;2023+2!=2025=45^{2}&lt;2023+3!+2029&lt;$ $2116=46^{2}$.
        · --Ainsi pour $\mathrm{n}=0,1,3,2023+\mathrm{n}$ ! n'est pas un carré,
          simp only [h2, Nat.factorial_zero, Nat.reduceAdd] at h
          obtain ⟨r, hr⟩ := h
          have hr1 : r < 45 := by
            have : 2024 < 45 * 45 := by norm_num
            rw [hr] at this
            exact Nat.mul_self_lt_mul_self_iff.mp this
          have hr2 : r > 44 := by
            have : 2024 > 44 * 44 := by norm_num
            rw [hr] at this
            exact Nat.mul_self_lt_mul_self_iff.mp this
          linarith
        · cases' h3 with h4 h5
          · simp only [h4, Nat.factorial_one, Nat.reduceAdd] at h
            obtain ⟨r, hr⟩ := h
            have hr1 : r < 45 := by
              have : 2024 < 45 * 45 := by norm_num  
              rw [hr] at this
              exact Nat.mul_self_lt_mul_self_iff.mp this
            have hr2 : r > 44 := by
              have : 2024 > 44 * 44 := by norm_num
              rw [hr] at this
              exact Nat.mul_self_lt_mul_self_iff.mp this
            linarith
          · cases' h5 with h6 h7
            · --mais pour $\mathrm{n}=2$ c'est un carré.
              contradiction
            · simp only [h7] at h
              obtain ⟨r, hr⟩ := h
              have h3! : Nat.factorial 3 = 6 := by 
                exact rfl
              rw [h3!] at hr
              simp only [Nat.reduceAdd] at hr
              have hr1 : r > 45 := by
                have : 2029 > 45 * 45 := by norm_num
                rw [hr] at this
                exact Nat.mul_self_lt_mul_self_iff.mp this
              have hr2 : r < 46 := by
                have : 2029 < 46 * 46 := by norm_num
                rw [hr] at this
                exact Nat.mul_self_lt_mul_self_iff.mp this
              linarith
    · --Ainsi $2023+\mathrm{n}$ ! est un carré si et seulement si $n=2$.
      intro hn
      simp only [hn, Nat.factorial_two, Nat.reduceAdd]
      use 45
--Commentaire des correcteurs : L'exercice a été très bien réussi. Quelques copies ont oublié le cas $\mathrm{n}=$ 0 .