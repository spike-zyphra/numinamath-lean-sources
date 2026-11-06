import Mathlib

def X (n : ℕ) : ℤ := match n with
  | 0 => 1
  | 1 => 1
  | n + 2 => X (n+1) + 2 * X (n)

def Y (n : ℕ) : ℤ := match n with
  | 0 => 1
  | 1 => 7
  | n + 2 => 2 * Y (n+1) + 3 * Y (n)

/- Let $\{X_n\}$ and $\{Y_n\}$ denote two sequences of integers defined as follows:

 $X_0=1$, $X_1=1$, $X_{n+1}=X_n+2X_{n-1}$ $(n=1,2,3,\dots),$
$Y_0=1$, $Y_1=7$, $Y_{n+1}=2Y_n+3Y_{n-1}$ $(n=1,2,3,\dots)$.
Thus, the first few terms of the sequences are:

 $X:1, 1, 3, 5, 11, 21, \dots$,
 $Y:1, 7, 17, 55, 161, 487, \dots$.
Prove that, except for the "1", there is no term which occurs in both sequences. -/
theorem number_theory_95883 : ∀ m n, X m = Y n → X m = 1 := by
  intro m n
  intro h
  
  --We prove that as long as for every a≥ 2 and b, X_a ≠ Y_b, so if X_m = Y_n, it can only occur at the beginning and hence X_m = 1.
  --We do this by considering mod 8.
  have cla : ∀ a b :ℕ, 2≤ a → (X a ≠ Y b) := by 
    have ind1 : ∀ i:ℕ, ∀ a:ℕ, (2≤ a ∧ a ≤ (i+2)) → (Even a → X a % 8 = 3) ∧ (Odd a → X a % 8 = 5) := by 
      intro i 
      induction' i with i hi
      simp
      intro a age2 ale2
      have aeq2 : a = 2 := by linarith
      simp [aeq2]
      have eq : X (2) = X (1) + 2 * X (0) := by simp [X]
      rw [show X 1 = 1 by simp [X], show X 0 = 1 by simp [X]] at eq
      rw [eq]; norm_num

      intro a ha
      obtain ⟨age2, al⟩ := ha
      by_cases ieq0 : i = 0
      simp_all
      by_cases aeq2 : a = 2 
      simp_all
      have aeq3 : a = 3 := by omega
      simp [aeq3]; constructor; intro even3; 
      have odd3 : Odd 3 := by use 1; simp
      contradiction
      intro odd3
      have eq : X (3) = X (2) + 2 * X (1) := by simp [X]
      have eq2 : X (2) = X (1) + 2 * X (0) := by simp [X]
      rw [eq2] at eq; simp [X]

      have ige1 : 1 ≤ i := by omega
      by_cases hb : a ≤ i+2
      apply hi; tauto
      have ieq : a = i + 3 := by omega
      have exik : ∃ k : ℕ, k + 2 = a := by use (a - 2); omega
      obtain ⟨k,hk⟩ := exik

      have eq : X (k + 2) = X (k + 1) + 2 * X (k) := by simp [X]

      by_cases aeven : Even a
      simp [aeven]
      have keven : Even k := by
        have : k = a - 2 := by omega
        rw [this]
        obtain ⟨j,hj⟩ := aeven
        use j-1; omega
      have kp1odd : Odd (k+1) := by exact Even.add_one keven
      have kleip2 : k ≤ i+2 := by omega
      have kp1leip2 : k + 1 ≤ i+2 := by omega
      have kge2 : 2 ≤ k := by omega
      have kp1ge2 : 2 ≤ k+1 := by omega
      have kk : 2≤ k ∧ k ≤ i+2 := by tauto
      have kpkp : 2 ≤ (k+1) ∧ (k+1) ≤ (i+2) := by tauto
      have kmod : X k % 8 = 3 := by
        apply hi at kk
        apply kk.left at keven
        assumption
      have kp1mod : X (k+1) % 8 = 5 := by
        apply hi at kpkp
        apply kpkp.right at kp1odd
        assumption
      rw [←hk, eq]; omega

      have aodd : Odd a := by exact Nat.not_even_iff_odd.mp aeven
      simp [aodd]
      have kodd : Odd k := by 
        have : k = a -2 := by omega
        rw [this]
        obtain ⟨j,hj⟩ := aodd
        use j-1; omega
      have kp1even : Even (k+1) := by exact Odd.add_one kodd
      have kleip2 : k ≤ i+2 := by omega
      have kp1leip2 : k + 1 ≤ i+2 := by omega
      have kge2 : 2 ≤ k := by omega
      have kp1ge2 : 2 ≤ k+1 := by omega
      have kk : 2≤ k ∧ k ≤ i+2 := by tauto
      have kpkp : 2 ≤ (k+1) ∧ (k+1) ≤ (i+2) := by tauto
      have kmod : X k % 8 = 5 := by
        apply hi at kk
        apply kk.right at kodd
        assumption
      have kp1mod : X (k+1) % 8 = 3 := by
        apply hi at kpkp
        apply kpkp.left at kp1even
        assumption
      rw [←hk, eq]; omega

    have ind2 : ∀ i:ℕ , ∀ b:ℕ, (b ≤ i) → (Even b → Y b % 8 = 1) ∧ (Odd b → Y b % 8 = 7) := by
      intro i
      induction' i with i hi
      intro b hb
      have beq0 : b = 0 := by linarith
      rw [beq0]; simp [Y]

      intro b hb
      by_cases blei: b ≤ i
      apply hi; exact blei

      have beqip1 : b = i+1 := by linarith
      by_cases ieq0 : i = 0
      have beq1 : b = 1 := by linarith
      rw [beq1]; simp [Y]
      have bge2 : 2 ≤ b := by omega
      have exik : ∃ k:ℕ, k + 2 = b := by use b-2; omega
      obtain ⟨k,hk⟩ := exik
      
      have eq : Y (k+2) = 2 * Y (k+1) + 3 * Y (k) := by simp [Y]

      by_cases beven : Even b
      simp [beven]
      have keven : Even k := by 
        have : k = b-2 := by omega
        rw [this];
        obtain ⟨j,hj⟩ := beven
        use j-1; omega
      have kp1odd : Odd (k+1) := by exact Even.add_one keven
      have klei : k ≤ i := by linarith
      have kp1lei : k + 1 ≤ i := by linarith
      have kmod : Y k % 8 = 1 := by 
        apply hi at klei
        apply klei.left at keven
        assumption
      have kp1mod : (Y (k+1))%8 = 7 := by
        apply hi at kp1lei
        apply kp1lei.right at kp1odd
        assumption
      rw [←hk, eq]; omega

      have bodd: Odd b := by exact Nat.not_even_iff_odd.mp beven
      simp [bodd]
      have kodd : Odd k := by
        have : k = b-2 := by omega
        rw [this];
        obtain ⟨j, hj⟩ := bodd
        use j-1; omega
      have kp1even : Even (k+1) := by exact Odd.add_one kodd
      have klei : k ≤ i := by linarith
      have kp1lei : k + 1 ≤ i := by linarith
      have kmod : Y k % 8 = 7 := by
        apply hi at klei
        apply klei.right at kodd
        assumption
      have kp1mod : (Y (k+1)) % 8 = 1 := by
        apply hi at kp1lei
        apply kp1lei.left at kp1even
        assumption
      rw [← hk, eq]; omega
      
    
    -- now just apply the lemmas we got to show that the only common elements can be 1.
    intro a b ha
    by_contra eq
    have cla1 : X a % 8 = 3 ∨ X a % 8 = 5 := by 
      have t : (Even a → X a % 8 = 3) ∧ (Odd a → X a % 8 = 5) := by
        apply ind1 a a
        constructor; linarith; linarith
      rcases t with ⟨t1,t2⟩
      by_cases evena : Even a
      apply t1 at evena; left; assumption
      have odda : Odd a := by exact Nat.not_even_iff_odd.mp evena
      apply t2 at odda; right; assumption
    have cla2 : Y b % 8 = 1 ∨ Y b % 8 = 7 := by
      have t : (Even b → Y b % 8 = 1) ∧ (Odd b → Y b % 8 = 7) := by apply ind2 b b; linarith
      rcases t with ⟨t1,t2⟩
      by_cases evenb : Even b
      apply t1 at evenb; left; assumption
      have oddb : Odd b := by exact Nat.not_even_iff_odd.mp evenb
      apply t2 at oddb; right; assumption
    rw [eq] at cla1
    rcases cla1 with (cla1l | cla1r)
    rcases cla2 with (cla2l | cla2r)
    linarith; linarith
    rcases cla2 with (cla2l | cla2r)
    linarith; linarith

  have ml2 : m < 2 := by
    by_contra mge2; push_neg at mge2
    apply cla m n
    assumption; assumption
  have : X m = 1 := by 
    by_cases meq0 : m = 0
    rw [meq0]; simp [X]
    have meq1 : m = 1 := by omega
    rw [meq1]; simp [X]
  assumption