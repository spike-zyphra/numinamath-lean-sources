import Mathlib

theorem number_theory_233883 (m n : ℕ) : Nat.factorial m + 12 = n^2 ↔ (m = 4 ∧ n = 6) := by 
  constructor
  · -- First direction: if m! + 12 = n^2 then m = 4 and n = 6
    intro h
    have h1 : m ≤ 4 := by 
      by_contra h2
      push_neg at h2
      have h5 : 5 ∣ Nat.factorial m := by 
        apply Nat.dvd_factorial
        all_goals linarith [show m >= 5 by omega]
      -- If $m \geq 5$, then $5$ divides $m!$. So $n^2 = m! + 12$, so $n^2 \equiv 12 \pmod{5} \equiv 2 \pmod{5}$. But $n^2 \bmod 5 \neq 2$ because quadratic residues mod 5 are {0, 1, 4}.
      -- Therefore impossible: contradiction leads to $m ≤ 4$.
      have h6 : n^2 % 5 = 2 % 5 := by
        have h7 : Nat.factorial m % 5 = 0 := by 
          exact Nat.dvd_iff_mod_eq_zero.mp h5
        omega
      -- Now showing contradiction because $n^2$ can't 2 mod 5
      have h8 : n^2 % 5 = 0 ∨ n^2 % 5 = 1 ∨ n^2 % 5 = 4 := by
        have h3 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
          omega
        rcases h3 with (h | h | h | h | h)
        · -- If n % 5 = 0, then n² % 5 = 0
          simp [Nat.pow_mod, h]
        · -- If n % 5 = 1, then n² % 5 = 1
          simp [Nat.pow_mod, h]
        · -- If n % 5 = 2, then n² % 5 = 4
          simp [Nat.pow_mod, h]
        · -- If n % 5 = 3, then n² % 5 = 4
          simp [Nat.pow_mod, h]
        · -- If n % 5 = 4, then n² % 5 = 1
          simp [Nat.pow_mod, h]
      omega
    have h2 : m ≤ 4 := h1
    -- bound on m, so finite cases.
    interval_cases m <;> try { 
      -- compute all factorial for m=0,1,2,3,4.
      norm_num [Nat.factorial] at h
      all_goals 
      have h4 : n ≤ 8 := by nlinarith
      interval_cases n <;> try { contradiction } <;> try { simp_all }
    }
  · -- Backward direction: if m=4 and n=6 then equation holds
    rintro ⟨rfl, rfl⟩
    norm_num [Nat.factorial]
    <;> try { rfl }
    <;> try { nlinarith }
    <;> try { native_decide }
    <;> try { tauto }
    <;> try { contradiction }
    <;> try { omega }