import Mathlib

/-
Let $K$ be a natural number such that $K \ge 8$. Define a sequence $f(n)$ by $f(0)=130$ and for $n \ge 0$, $f(n+1) = f(n)/2 + 2$ if $f(n)$ is even, and $f(n+1) = 2 f(n) - 2$ if $f(n)$ is odd. Show that $f(K)$ is $6$ if $(K-8) \pmod 3 = 0$, $f(K)$ is $5$ if $(K-8) \pmod 3 = 1$, and $f(K)$ is $8$ if $(K-8) \pmod 3 = 2$.
-/

theorem number_theory_641816 (K:ℕ) (hK: K ≥ 8) (f : ℕ → ℕ) (h0: f 0 = 130) (hf: (∀ n, Even (f n) → f (n+1) = f (n) /2 + 2) ∧ (∀ n, Odd (f n) → f (n+1) = 2 * f n - 2)):
  ((K-8) % 3 = 0 → f K = 6) ∧ ((K-8) % 3 = 1 → f K = 5) ∧ ((K-8) % 3 = 2 → f K = 8) := by

  obtain ⟨ef,of⟩ := hf

  --We first calculate the first 10 values.
  have h1 : f 1 = 67 := by
    specialize ef 0 
    have : Even (f 0) := by simp [h0]; decide 
    simp [this] at ef
    simp [h0] at ef
    exact ef
  have h2 : f 2 = 132 := by
    specialize of 1 
    have : Odd (f 1) := by simp [h1]; decide 
    simp [this] at of
    simp [h1] at of
    exact of
  have h3 : f 3 = 68 := by
    specialize ef 2
    have : Even (f 2) := by simp [h2]; decide 
    simp [this] at ef
    simp [h2] at ef
    exact ef
  have h4 : f 4 = 36 := by 
    specialize ef 3
    have : Even (f 3) := by simp [h3]; decide 
    simp [this] at ef
    simp [h3] at ef
    exact ef
  have h5 : f 5 = 20 := by 
    specialize ef 4 
    have : Even (f 4) := by simp [h4]; decide 
    simp [this] at ef
    simp [h4] at ef
    exact ef
  have h6 : f 6 = 12 := by 
    specialize ef 5
    have : Even (f 5) := by simp [h5]; decide 
    simp [this] at ef
    simp [h5] at ef
    exact ef
  have h7 : f 7 = 8  := by 
    specialize ef 6 
    have : Even (f 6) := by simp [h6]; decide 
    simp [this] at ef
    simp [h6] at ef
    exact ef
  have h8 : f 8 = 6  := by 
    specialize ef 7 
    have : Even (f 7) := by simp [h7]; decide 
    simp [this] at ef
    simp [h7] at ef
    exact ef
  have h9 : f 9 = 5  := by 
    specialize ef 8 
    have : Even (f 8) := by simp [h8]; decide 
    simp [this] at ef
    simp [h8] at ef
    exact ef
  have h10: f 10= 8  := by
    specialize of 9 
    have : Odd (f 9) := by simp [h9]; decide 
    simp [this] at of
    simp [h9] at of
    exact of


  --Our claim follows from the following induction that from f 8, the value of f goes like 6 5 8 6 5 8...
  have cla : ∀ l:ℕ, f (3*l+8) = 6 ∧ f (3*l+9) = 5 ∧ f (3*l+10) = 8 := by 
    intro l
    induction' l with l hl

    simp [h8,h9,h10]

    obtain ⟨h8,h9,h10⟩ := hl
    have h11 : f (3 * (l + 1) + 8) = 6 := by 
      specialize ef (3*l+10)
      have : Even (f (3*l+10)) := by simp [h10]; decide
      simp [this] at ef
      simp [h10] at ef
      have : 3*(l+1)+8 = 3*l+10+1 := by ring
      rw [this]
      exact ef

    have h12 : f (3 * (l + 1) + 9) = 5 := by 
      ring_nf at h11 ⊢
      specialize ef (11+l*3)
      have : Even (f (11+l*3)) := by 
        simp [h11]; decide
      simp [this] at ef
      simp [h11] at ef
      have : 12 + l * 3 = 11 + l * 3 + 1 := by ring
      rw [this]
      exact ef

    have h13 : f (3 * (l + 1) + 10) =8 := by 
      ring_nf at h12 ⊢
      specialize of (12+l*3)
      have : Odd (f (12+l*3)) := by 
        simp [h12]; decide
      simp [this] at of
      simp [h12] at of
      have : 13 + l * 3 = 12 + l * 3 + 1 := by ring
      rw [this]
      exact of

    simp [h11,h12,h13] 

  by_cases m0 : (K-8) % 3 = 0
  simp [m0]
  have : 3 ∣ K-8 := by exact Nat.dvd_of_mod_eq_zero m0
  obtain ⟨d,hd⟩ := this
  have exi : ∃ l:ℕ, 3 * l + 8 = K := by 
    use d
    omega
  obtain ⟨l,hl⟩ := exi
  specialize cla l
  obtain ⟨cor,_,_⟩ := cla
  rw [hl] at cor
  exact cor

  by_cases m1 : (K-8) % 3 = 1
  simp [m1]
  have : 3 ∣ K-8-1 := by 
    refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm m1))
    omega
  obtain ⟨d,hd⟩ := this
  have exi : ∃ l:ℕ, 3 * l + 9 = K := by 
    use d
    omega
  obtain ⟨l,hl⟩ := exi
  specialize cla l
  obtain ⟨_,cor,_⟩ := cla
  rw [hl] at cor
  exact cor

  have m2 : (K-8) % 3 = 2 := by omega
  simp [m2]
  have : 3 ∣ K-8-2 := by 
    refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm m2))
    omega
  obtain ⟨d,hd⟩ := this
  have exi : ∃ l:ℕ, 3 * l + 10 = K := by 
    use d
    omega
  obtain ⟨l,hl⟩ := exi
  specialize cla l
  obtain ⟨_,_,cor⟩ := cla
  rw [hl] at cor
  exact cor