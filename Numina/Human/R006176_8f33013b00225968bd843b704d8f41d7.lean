import Mathlib

/-
Find the number of positive integer solutions to $ \frac { 1 } { x } + \frac { 1 } { y } = \frac { 1 } { 2 0 2 0 } $.
-/

theorem number_theory_629014 :
{(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ (1 / x : ℚ) + (1 / y : ℚ) = 1 / (2020 : ℚ)}.encard = 45 := by 

  let S := {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ (1 / x : ℚ) + (1 / y : ℚ) = 1 / (2020 : ℚ)}

  --2020^2 has 45 divisors and we will prove that the number of solutions equal the number of divisors of 2020^2.
  have cla : (Nat.divisors (2020^2)).card = 45 := by native_decide
  have : S.encard = (Nat.divisors (2020^2)).card := by 

    --Let f be function mapping a pair (a,b) in S to a-2020.
    let f : (ℕ × ℕ) → ℕ := fun (x, y) => x - 2020

    --We will prove that f is injective on S and f '' S is exactly Nat.divisors (2020 ^ 2).
    --All are simple calculation by the assumptions.
    have finj : Set.InjOn f S := by 
      unfold Set.InjOn
      intro ⟨x1,y1⟩ h1 ⟨x2,y2⟩ h2 heq
      simp
      simp [f] at heq
      simp [S] at h1 h2
      obtain ⟨x1pos,y1pos,h1⟩ := h1
      obtain ⟨x2pos,y2pos,h2⟩ := h2
      field_simp at h1 h2 
      
      have t1: 2020 < x1 := by 
        qify; 
        have b1: (x1:ℚ)*2020 = (x1-2020)*y1 := by linarith
        have b2: 0 < (x1:ℚ)*2020 := by qify at x1pos; linarith
        have b3: 0 < (x1-2020)*(y1:ℚ) := by linarith
        qify at y1pos
        have : 0 < ((x1:ℚ)-2020) := by nlinarith only [b3,y1pos]
        linarith only [this]
        
      have t2: 2020 < x2 := by
        qify; 
        have b1: (x2:ℚ)*2020 = (x2-2020)*y2 := by linarith
        have b2: 0 < (x2:ℚ)*2020 := by qify at x2pos; linarith
        have b3: 0 < (x2-2020)*(y2:ℚ) := by linarith
        qify at y2pos
        have : 0 < ((x2:ℚ)-2020) := by nlinarith only [b3,y2pos]
        linarith only [this]
      
      have x1eqx2: x1 =x2 := by omega

      rw [x1eqx2] at h1
      have : ((y1:ℚ) - y2) * (2020-x2) = 0 := by linarith
      rcases eq_zero_or_eq_zero_of_mul_eq_zero this with e1 | e2
      have : (y1 : ℚ)  = (y2 : ℚ) := by linarith
      simp at this
      simp [x1eqx2, this]
      qify at t2
      linarith


    have imaf : (f '' S) = (Nat.divisors (2020^2)) := by 
      simp [S,f]
      ext z
      simp

      constructor
      intro h
      obtain ⟨a, h⟩ := h
      obtain ⟨h, fam⟩ := h
      obtain ⟨apos,b,bpos, h⟩ :=h
      field_simp at h
      use (b-2020)

      have : (b+a) * 2020 = a * b := by qify; exact h
      have al: 2020 < a := by 
        zify at apos bpos this ⊢
        have : (a:ℤ)*2020 = (a-2020) * b := by linarith
        have : 0 < (a:ℤ)*2020 := by linarith
        have : 0 < ((a:ℤ)-2020) * b := by linarith
        have : 0 < ((a:ℤ))-2020 := by nlinarith only [bpos, this]
        linarith only [this]
      have bl: 2020 < b := by 
        zify at apos bpos this ⊢
        have : (b:ℤ)*2020 = (b-2020) * a := by linarith
        have : 0 < (b:ℤ)*2020 := by linarith
        have : 0 < ((b:ℤ)-2020) * a := by linarith
        have : 0 < ((b:ℤ))-2020 := by nlinarith only [apos, this]
        linarith only [this]

      rw [← fam]
      zify at this ⊢
      have : @Nat.cast ℤ AddMonoidWithOne.toNatCast (a - 2020) = (a-2020) := by omega
      rw [this]
      have : @Nat.cast ℤ AddMonoidWithOne.toNatCast (b - 2020) = (b-2020) := by omega
      rw [this]
      linarith
      

      intro h
      have zpos : 0 < z := by 
        by_contra znpos
        have ze : z = 0 := by omega
        rw [ze] at h
        simp at h

      use z + 2020
      simp
      use (2020^2 / z + 2020)
      simp
      field_simp
      ring_nf

    apply Set.InjOn.encard_image at finj
    rw [imaf] at finj
    rw [← finj]
    simp
    
  
  rw [cla] at this
  simp [S] at this ⊢
  exact this
  