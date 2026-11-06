import Mathlib

/-
3.3.14 ** The sequence $\left\{a_{n}\right\}$ is defined by the following conditions: $a_{1}=1, a_{n+1}=a_{n}+\frac{1}{a_{n}}, n \geqslant 1$, find the integer part of $a_{100}$.
-/

theorem algebra_179977 (a : ℕ → ℝ) (ha1: a 1 = 1) (h: ∀n≥1, a (n+1) = a n + 1 / (a n)) : ⌊a 100⌋ = 14 := by 
  
  refine Int.floor_eq_iff.mpr ?_
  simp
  ring_nf

  --Some basic facts needed later.
  have apos : ∀ n≥1, 0 < a n := by
    have cla : ∀ m:ℕ, 0 < a (m+1) := by
      intro m
      induction' m with m hm
      simp [ha1]

      specialize h (m+1)
      have : m+1 ≥ 1 := by linarith
      apply h at this
      rw [this]
      positivity
    intro n hn
    have exi : ∃ k:ℕ, n = k + 1 := by use n-1; omega
    obtain ⟨k,hk⟩ := exi
    specialize cla (k)
    rw [← hk] at cla
    exact cla
  have ooapos : ∀ n ≥ 1, 0 < 1/(a n) := by
    intro n hn
    specialize apos n (hn)
    exact one_div_pos.mpr apos
  have ooa2pos : ∀ n ≥ 1, 0 < 1/((a n))^2 := by 
    intro n hn
    specialize apos n hn
    have : 0 < (a n)^2 := sq_pos_of_pos apos
    exact one_div_pos.mpr this
  -- a_n is increasing, in particular, a n ≥ a 2 for every n ≥ 2.
  have agea2 : ∀ n ≥ 2, a 2 ≤ a n := by 
    have cla : ∀ m:ℕ, a 2 ≤ a (m+2) := by
      intro m
      induction' m with m hm

      simp

      specialize h (m+2) (by linarith)
      rw [add_assoc]
      nth_rw 2 [add_comm]
      rw [←add_assoc]
      rw [h]
      specialize ooapos (m+2) (by linarith)
      linarith
    intro n hn
    have exi : ∃ k:ℕ, n = k + 2 := by use n-2; omega
    obtain ⟨k,hk⟩ := exi
    specialize cla (k)
    rw [← hk] at cla
    exact cla
  have a2 : a 2 = 2 := by 
    simp [h, ha1]
    norm_num
  

  --We rewrite the assumption h to get the following formula
  have eq : ∀ n ≥ 1, (a (n+1))^2 - (a n)^2 = 2 + 1 / (a n)^2 := by 
    intro n hn
    specialize h n (by linarith)
    have : 0 < a n := apos n hn
    rw [h]
    ring_nf
    field_simp

  --Adding all the terms, we have a formula for a_n^2. We use this give bounds on a_n^2 in the following two claims.
  have cla1 : ∀ n≥1, 2*(n-1) ≤ (a n)^2 - (a 1)^2 := by 
    have tmp : ∀ m:ℕ, 2*((m+1)-1) ≤ (a (m+1))^2 - (a 1)^2 := by
      intro m
      induction' m with m hm

      simp

      have : a (m + 1 + 1) ^ 2 - a 1 ^ 2 = (a (m + 1 + 1) ^ 2 - (a (m+1)^2) ) + ((a (m+1)^2)- a 1 ^ 2) := by ring
      rw[this]
      specialize eq (m+1) (by linarith)
      rw [eq]
      specialize ooa2pos (m+1) (by linarith)
      ring_nf at hm ooa2pos ⊢
      have : ↑(1 + m) * 2 ≤ 2 + (a (1 + m) ^ 2 - a 1 ^ 2) := by
        field_simp
        rw [add_mul]
        ring_nf
        field_simp
        exact hm
      linarith
    intro n hn
    have exi : ∃ k:ℕ, k+1 = n := by use n-1; omega
    obtain ⟨k,hk⟩ := exi
    specialize tmp k
    rw [← hk]
    rify at hk
    field_simp at tmp ⊢
    exact tmp
  have cla2 : ∀ n≥2, (a n)^2 - (a 1)^2 ≤ 2 * (n-1) + 1 + (n-2)/4 := by 
    have tmp : ∀ m:ℕ, (a (m+2))^2 - (a 1)^2 ≤ 2 * ((m+2)-1) + 1 + ((m+2)-2)/4 := by 
      intro m
      induction' m with m hm

      simp [ha1,a2]
      norm_num
      have : a (m + 1 + 2) ^ 2 - a 1 ^ 2 = (a (m + 2 + 1) ^ 2 - (a (m+2)^2) ) + ((a (m+2)^2)- a 1 ^ 2) := by ring
      rw[this]
      specialize eq (m+2) (by linarith)
      rw [eq]
      have : 2 + 1 / a (m + 2) ^ 2 + (a (m + 2) ^ 2 - a 1 ^ 2) ≤ 2 + 1 / a (m + 2) ^ 2 + 2 * (↑m + 2 - 1) + 1 + (↑m + 2 - 2) / 4 := by linarith
      have : 2 + 1 / a (m + 2) ^ 2 + 2 * (↑m + 2 - 1) + 1 + (↑m + 2 - 2) / 4 ≤ 2 * (↑(m + 1) + 2 - 1) + 1 + (↑(m + 1) + 2 - 2) / 4 := by 
        ring_nf
        field_simp
        ring_nf

        have : (a (2 + m))⁻¹ ^ 2 ≤ 1/4 := by
          field_simp
          have : 4 ≤ a (2+m) ^ 2 := by
            have : 2 ≤ 2+m := by linarith
            specialize agea2 (2+m) this
            rw [a2] at agea2
            nlinarith
          refine one_div_le_one_div_of_le ?_ this
          linarith
        linarith
      linarith
    intro n hn
    have exi : ∃ k:ℕ, k+2 = n := by use n-2;omega
    obtain ⟨k,hk⟩ := exi
    specialize tmp k
    rw [← hk]
    rify at hk
    field_simp at tmp ⊢
    exact tmp

  --Now, we have 199 ≤ (a 100)^2 <225, so the ineger part of a 100 is 14.
  specialize cla1 100 (by linarith)
  specialize cla2 100 (by linarith)
  simp [ha1] at cla1 cla2

  have lb: 199 ≤ (a 100)^2 := by linarith
  have ub: (a 100)^2 < 225 := by nlinarith

  have : 14 ≤ a 100 := by
    specialize apos 100 (by linarith)
    have : 14^2 ≤ (a 100)^2 := by linarith
    rw [sq_le_sq₀] at this
    exact this
    linarith
    linarith
  have : a 100 < 15 := by nlinarith
  tauto


