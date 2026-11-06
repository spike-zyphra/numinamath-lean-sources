import Mathlib

lemma l₁ {Q R S : ℕ}
  (s_in : S ∈ [1, 2, 3, 4, 5])
  (five_dvd : 5 ∣ Nat.ofDigits 10 [S, R, Q]) :
    S = 5 := by
  simp_all [Nat.ofDigits]
  have mod_lemma : S % 10 = 0 ∨ S % 10 = 5 := by
    omega

  omega

lemma l₂ {P Q R : ℕ}
  (q_ne_r : Q ≠ R)
  (q_in : Q ∈ [1, 2, 3, 4])
  (r_in : R ∈ [1, 2, 3, 4, 5])
  (four_dvd : 4 ∣ Nat.ofDigits 10 [R, Q, P])
  : (R = 2 ∧ (Q = 1 ∨ Q = 3)) ∨ (R = 4 ∧ Q = 2) := by

  have : 4 ∣ 100 * P + 10 * Q + R := by
    convert four_dvd
    simp [Nat.ofDigits]
    ring

  have : 4 ∣ 2*Q + R := by
    omega

  mod_cases (2*Q + R) % 4
  all_goals
    simp_all
    omega

lemma l₃ {P Q R T : ℕ}
  (nodup : [P, Q, R, 5, T].Nodup)
  (t_in : T ∈ [1, 2, 3, 4, 5])
  (four_dvd : 4 ∣ Nat.ofDigits 10 [R, Q, P])
  (three_dvd : 3 ∣ Nat.ofDigits 10 [T, 5, R])
  (r_eq_or : (R = 2 ∧ (Q = 1 ∨ Q = 3)) ∨ (R = 4 ∧ Q = 2)) :
    R = 4 := by
  simp_all [Nat.ofDigits]
  rcases r_eq_or with (⟨ r_eq, h ⟩ | ⟨ r_eq, h ⟩)
  · subst R
    simp_all
    cases h
    · subst Q
      simp_all
      omega
    ·
      omega
  · omega

lemma l₄ {T : ℕ}
  (t_in : T ∈ [1, 2, 3, 4, 5])
  (three_dvd : 3 ∣ Nat.ofDigits 10 [T, 5, 4]) :
    T = 3 := by
  simp [Nat.ofDigits] at *
  omega

lemma l₅ {P Q : ℕ}
  (q_in : Q ∈ [1, 2, 3, 4, 5])
  (q_ne_4 : Q ≠ 4)
  (four_dvd : 4 ∣ Nat.ofDigits 10 [4, Q, P]) :
    Q = 2 := by
  simp [Nat.ofDigits] at *
  omega

theorem number_theory_301849 (P Q R S T : ℕ)
  (digits_in : [P, Q, R, S, T] ∈ [1, 2, 3, 4, 5].permutations)
  (three_dvd : 3 ∣ Nat.ofDigits 10 [T, S, R])
  (four_dvd : 4 ∣ Nat.ofDigits 10 [R, Q, P])
  (five_dvd : 5 ∣ Nat.ofDigits 10 [S, R, Q])
  : [P, Q, R, S, T] = [1, 2, 4, 5, 3] := by

  simp at digits_in
  let contains := λ x => List.Perm.contains_eq
      (l₁ := [P, Q, R, S, T]) (l₂ := [1, 2, 3, 4, 5]) (a := x) digits_in

  have nodup : [P, Q, R, S, T].Nodup := by
    have : [1, 2, 3, 4, 5].Nodup := by decide
    exact List.Perm.nodup (id (List.Perm.symm digits_in)) this

  have s_in : S ∈ [1, 2, 3, 4, 5] := by
    simpa using contains S

  have s_eq := l₁ s_in five_dvd
  subst s_eq

  have q_in : Q ∈ [1, 2, 3, 4] := by
    have := contains Q
    have : Q ≠ 5 := by
      intro eq
      simp [List.cons_perm_iff_perm_erase] at this
      subst Q
      simp_all

    simp_all [List.cons_perm_iff_perm_erase]

  have r_in : R ∈ [1, 2, 3, 4, 5] := by
    simpa using contains R

  have r_eq_or := l₂ (by simp_all) q_in r_in four_dvd

  have t_in : T ∈ ({1, 2, 3, 4, 5} : Finset ℕ) := by
    simpa using contains T

  have r_eq := by
    exact l₃ nodup t_in four_dvd three_dvd r_eq_or

  have p_in : P ∈ [1, 2, 3, 4, 5] := by
    simpa using contains P

  subst r_eq

  have q_in : Q ∈ ({1, 2, 3, 4, 5} : Finset ℕ) := by
    simpa using contains Q

  have t_eq := l₄ t_in three_dvd
  subst t_eq

  have q_eq := l₅ q_in (by omega) four_dvd
  subst q_eq

  simp_all
