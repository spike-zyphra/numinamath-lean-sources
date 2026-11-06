import Mathlib

lemma lemma_1
  (n : ℕ)
  (hn : Even n)
  : n^2 % 4 = 0 :=
by
  rcases hn with ⟨n', hn⟩
  rw [hn, show (n' + n')^2 = 4 * n'^2 by linarith]
  simp

lemma lemma_2
  (n : ℕ)
  (hn : Odd n)
  : n^2 % 4 = 1 :=
by
  rcases hn with ⟨n', hn⟩
  rw [hn]
  ring_nf
  simp

/- Let $D$ be an even natural number greater than 0. Let $m, n, k$ be natural numbers such that $D$ divides $(m+n+k)$ and $D^2$ divides $(m^2+n^2+k^2)$. Prove that $8$ divides $(m^3+n^3+k^3)$. -/
theorem number_theory_641659 (D m n k : ℕ) (hD : Even D) (hD1 : D > 0)
    (hD2 : D ∣ (m + n + k)) (hD3 : D ^ 2 ∣ (m ^ 2 + n ^ 2 + k ^ 2)) :
    8 ∣ (m ^ 3 + n ^ 3 + k ^ 3) :=
by
  rcases hD with ⟨D', hD4⟩
  -- m + n + k is divisible by 2
  have : 2 ∣ m + n + k := by
    rw [hD4, show D' + D' = 2 * D' by omega] at hD2
    exact dvd_of_mul_right_dvd hD2
  -- m^2 + n^2 + k^2 is divisible by 4
  have : 4 ∣ m^2 + n^2 + k^2 := by
    rw [hD4] at hD3
    rw [show (D' + D')^2 = 4 * D'^2 by linarith] at hD3
    exact dvd_of_mul_right_dvd hD3
  -- Use the lemma we have been proved, 
  -- We can show that each one of m, n, k is even number
  have : Even m ∧ Even n ∧ Even k := by
    by_contra h
    simp at h
    rcases em (Even m) with (hm|hm)
    rcases em (Even n) with (hn|hn)
    . have : (m ^ 2 + n ^ 2 + k ^ 2) % 4 = 1 := by
        rw [Nat.add_mod, Nat.add_mod (m^2)]
        rw [lemma_1, lemma_1, lemma_2]
        all_goals tauto
      omega
    rcases em (Even k) with (hk|hk)
    . simp at hn
      have : (m ^ 2 + n ^ 2 + k ^ 2) % 4 = 1 := by
        rw [Nat.add_mod, Nat.add_mod (m^2)]
        rw [lemma_1, lemma_2, lemma_1]
        all_goals try tauto
      omega
    . simp at hn hk
      have : (m ^ 2 + n ^ 2 + k ^ 2) % 4 = 2 := by
        rw [Nat.add_mod, Nat.add_mod (m^2)]
        rw [lemma_1, lemma_2, lemma_2]
        all_goals tauto
      omega
    simp at hm
    rcases em (Even n) with (hn|hn)
    rcases em (Even k) with (hk|hk)
    . have : (m ^ 2 + n ^ 2 + k ^ 2) % 4 = 1 := by
        rw [Nat.add_mod, Nat.add_mod (m^2)]
        rw [lemma_2, lemma_1, lemma_1]
        all_goals tauto
      omega
    . simp at hk
      have : (m ^ 2 + n ^ 2 + k ^ 2) % 4 = 2 := by
        rw [Nat.add_mod, Nat.add_mod (m^2)]
        rw [lemma_2, lemma_1, lemma_2]
        all_goals tauto
      omega
    simp at hn
    rcases em (Even k) with (hk|hk)
    . have : (m ^ 2 + n ^ 2 + k ^ 2) % 4 = 2 := by
        rw [Nat.add_mod, Nat.add_mod (m^2)]
        rw [lemma_2, lemma_2, lemma_1]
        all_goals tauto
      omega
    . simp at hk
      have : (m ^ 2 + n ^ 2 + k ^ 2) % 4 = 3 := by
         rw [Nat.add_mod, Nat.add_mod (m^2)]
         repeat rw [lemma_2]
         all_goals tauto
      omega
  rcases this with ⟨⟨m, mh⟩, ⟨n, nh⟩, ⟨k, kh⟩⟩
  rw [mh, nh, kh]
  ring_nf
  repeat rw [←add_mul]
  simp
