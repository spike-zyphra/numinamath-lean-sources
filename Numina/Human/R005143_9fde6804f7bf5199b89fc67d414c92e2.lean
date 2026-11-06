import Mathlib

/- Find all functions $f: \mathbb{N} \rightarrow \mathbb{N}$ such that

$$
n!+f(m)!\mid f(n)!+f(m!)
$$

for all $m, n \in \mathbb{N}$. -/

open Nat

-- Nat.exists_infinite_primes


theorem number_theory_605785 (f : ℕ → ℕ) :
    (∀ m n, Nat.factorial n + Nat.factorial (f m) ∣ Nat.factorial (f n) + (f (Nat.factorial m))) ↔
    (∀ n, (n = 0 → f n = 1 ∨ f n = 0) ∧ (n ≥ 1 → f n = n)) := by 
  constructor
  · 
    intro h
    obtain dvd1 := h 1 1 
    simp at dvd1
    have dvd2 : (1 + (f 1)! : ℤ) ∣ f 1 - 1 := by 
      have aux :  (1 + (f 1)! : ℤ) ∣ (f 1)! + (f 1) := by 
        norm_cast
      have aux1 : ((f 1) : ℤ) - 1 = (f 1)! + (f 1) - (1 + ↑(f 1)!) := by ring
      rw [aux1]
      exact dvd_sub_self_right.mpr aux
    have absle : |(f 1 : ℤ) - 1| < (f 1)! + 1 := by 
      unfold abs
      simp
      constructor
      have absge : ((f 1)! : ℤ) ≥ f 1 := by 
        refine Int.ofNat_le.mpr ?_
        exact self_le_factorial (f 1)
      linarith
      have aux : ((f 1)! : ℤ) ≥ 1 := by 
        norm_cast
        linarith [Nat.factorial_pos (f 1)]
      have aux1 : ((f 1) : ℤ) ≥ 0 := by 
        norm_cast
        positivity
      linarith
    have eq1 : ((f 1) : ℤ) - 1= 0 := by 
      refine Int.eq_zero_of_abs_lt_dvd dvd2 ?_
      linarith
    have feq1 : f 1 = 1 := by 
      linarith
    have fnpos (n : ℕ) (npos : n > 0 ): f n > 0 := by 
        by_contra hc'
        simp at hc'
        obtain dvd3' := h 1 n
        simp [feq1] at dvd3'
        have aux : n ! + 1 ≤ (f n)! + 1  := by 
          exact Nat.le_of_dvd (by positivity) dvd3'
        have aux' : n ! ≤ (f n)!  := by
          linarith
        rw [hc'] at aux'
        simp at aux'
        by_cases hn1 : n = 1
        rw [hn1, feq1] at hc'
        linarith
        have nge2 : n ≥ 2 := by 
          omega
        have ineq : n ! ≥ 2 ! := by 
          apply Nat.factorial_le nge2
        simp at ineq
        linarith

    -- take m = 1, then we have  `∀ (n : ℕ), n ! + (f 1)! ∣ (f n)! + f 1!`
    obtain dvd3 := h 1 
    have ineq1 : ∀ n, n ≥ 2 → f n ≥ n := by 
      intro n hn
      obtain dvd3' := dvd3 n
      simp [feq1] at dvd3'
      have aux : n ! + 1 ≤ (f n)! + 1  := by 
        exact Nat.le_of_dvd (by positivity) dvd3'
      have aux' : n ! ≤ (f n)!  := by
        linarith
      by_contra hc
      simp at hc
      obtain h1 := (Nat.factorial_lt (fnpos n (by linarith))).mpr hc
      linarith
    have ineq2 : ∀ n, n ≥ 1 → f n ≥ n := by 
      intro n hn
      by_cases hneq1 : n = 1
      rw [hneq1, feq1]
      have nge2 : n ≥ 2 := by omega
      exact ineq1 n nge2
    -- for prime number p, prove that f (p - 1) = p - 1 by provting that f (p - 1) < p
    have hp1 : ∀ p, Nat.Prime p → f (p - 1) = p - 1 := by 
      intro p hp
      obtain h1 := h 1 (p - 1)
      simp [feq1] at h1
      have le1 : p - 1 ≥ 1 := by 
        have pge2 : p ≥ 2 := by 
          exact Prime.two_le hp
        omega
      obtain fpineq := ineq2 (p- 1) le1
      have pdvd : p ∣ (p - 1)! + 1 := by 
        have wilson_dvd : (p : ℤ) ∣ (p - 1)! + 1 := by 
          have fact1 : Fact (Nat.Prime p) := by 
            exact { out := hp }
          obtain h2 := ZMod.wilsons_lemma p
          have h3 : (p -1) ! ≡  - 1 [ZMOD p] := by 
            refine (ZMod.intCast_eq_intCast_iff (↑(p - 1)!) (-1) p).mp ?_
            simp [h2]
          obtain h4 := Int.ModEq.dvd (Int.ModEq.symm h3)
          simp at h4
          exact h4
        norm_cast at wilson_dvd
      have pdvd2 : p ∣ (f (p - 1))! + 1 := by 
        exact Nat.dvd_trans pdvd h1
      -- if f (p - 1) ≥ p, then ¬ p ∣ (f (p - 1))! + 1, which contradicts to pdvd2
      have fpineq2 : f (p - 1) < p := by 
        by_contra hc
        simp at hc
        have pdvd3 : p ∣ (f (p - 1)) ! := by 
          apply Nat.dvd_factorial
          exact Prime.pos hp
          exact hc
        have pdvd4 : p ∣ 1 := by 
          exact (Nat.dvd_add_iff_right pdvd3).mpr pdvd2
        norm_num at pdvd4
        rw [pdvd4] at hp
        norm_num at hp
      have fpineq3 : f (p - 1) ≤ p - 1 := by 
        omega
      linarith
    have hp2 : ∀ p m, Nat.Prime p → (p - 1) ! + (f m)! ∣ (p - 1)! + (f (m !)) := by
      intro p m hp
      obtain h1 := hp1 p hp
      conv => 
        rhs
        rw [←h1]
      exact h m (p - 1)
    have hp3 : ∀ p m, Nat.Prime p → (p - 1) ! + (f m)! ∣ f (m !) - (f m)! := by 
      intro p m hp
      obtain h1 := h m (p - 1)
      rw [hp1 p hp] at h1
      have aux : f m ! - (f m)! = (p - 1)! + f m ! - ((p - 1)! + (f m)!) := by 
        omega
      rw [aux]
      have dvd1 : (p - 1)! + (f m)! ∣ (p - 1)! + (f m)! := by 
        simp
      exact dvd_sub' (hp2 p m hp) dvd1
    have eq2 : ∀ m, f (m !) = (f m)! := by 
      intro m
      obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes ((f (m !)) + 2)
      obtain h1 := hp3 p m hp
      have ineq_aux : (p - 1)! + (f m)! > |f m ! - ((f m)! : ℤ)| := by 
        unfold abs
        simp
        constructor
        have aux : ((p - 1)! ) ≥ p - 1 := by 
          exact self_le_factorial (p - 1)
        have aux1 : (p - 1) > (f (m !)) := by 
          omega
        have aux2 : (f m)! > 0 := by 
          exact factorial_pos (f m)
        zify at aux aux1 aux2
        calc 
          _ < (f m ! : ℤ) := by 
            linarith
          _ < ((p - 1) ! : ℤ) := by 
            linarith
          _ < _ := by 
            linarith
        have pos1 : (f m ! : ℤ) ≥  0 := by 
          norm_cast
          linarith
        have aux1 : (↑(p - 1)! : ℤ) ≥ 1 := by 
          norm_cast
          linarith [factorial_pos ((p - 1))]
        linarith
      have  h2 : (f m ! : ℤ) - (f m)! = 0 := by 
        refine Int.eq_zero_of_abs_lt_dvd ?_ ineq_aux
        zify at h1
        have aux1 : ((f m ! - (f m)! : ℕ) : ℤ) = (f m ! : ℤ) - (f m)!  := by 
          have aux2 : f m ! ≥  (f m)! := by 
            obtain aux3 := le_of_dvd (by positivity) (hp2 p m hp)
            linarith
          omega
        rw [aux1] at h1
        exact h1
      zify
      linarith
    have dvd4 : ∀ n m, (n ! + (f m)! : ℤ) ∣ (f n)! - n ! := by 
      intro n m
      obtain aux1 := h m n
      obtain aux2 := eq2 m
      rw [aux2] at aux1
      have aux : ↑(f n)! - (n ! : ℤ) = (f n)! + (f m)! - (n ! + (f m)!) := by 
        ring
      rw [aux]
      zify at aux1
      exact dvd_sub_self_right.mpr aux1

    intro n
    -- take m large enough, for example m = (f n)!
    obtain dvd5 := dvd4 n (n)
    have absle2 : |(f n)! -(n ! : ℤ)| < n ! + (f n)! := by
      unfold abs
      simp
      constructor
      linarith [factorial_pos n]
      linarith [factorial_pos (f n)]
    have eq3 : ((f n)! : ℤ) - n ! = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd dvd5 ?_
      linarith
    have eq4 : ((f n)! : ℤ) = n ! := by 
      linarith
    norm_cast at eq4
    obtain h1 := h 0 1
    simp [feq1] at h1 
    have ineq2 : (f 0)! ≤ 1 := by 
      obtain ineq2 :=  Nat.le_of_dvd (by positivity) h1
      linarith
    obtain h2 := h 1 0 
    simp [feq1] at h2
    have ineq3 : (f 0)! ≥ 1 := by 
      obtain ineq3 := Nat.le_of_dvd (by positivity) h2
      linarith
    have eq5 : (f 0)! = 1 := by 
      exact eq_of_le_of_le ineq2 ineq3
    constructor
    · -- the cases n = 0
      intro hn0
      rw [hn0]
      refine Or.symm ((fun {n} => le_one_iff_eq_zero_or_eq_one.mp) ?_)
      simp at eq5
      exact eq5
    · -- the cases n ≥ 1
      intro hn1
      by_cases hneq1 : n = 1
      simp [hneq1,feq1]
      have ngt1 : n > 1 := by 
        omega
      exact Eq.symm ((Nat.factorial_inj ngt1).mp (Eq.symm eq4))
  · 
    intro h
    intro m n
    have feq1 : f 1 = 1 := by 
      obtain aux := (h 1).2 (by linarith)
      exact aux
    -- discuss the cases m = 1
    by_cases hm0 : m = 0
    obtain hmeq := (h m).1 hm0
    obtain hmeq | hmeq := hmeq
    rw [hmeq, hm0]
    by_cases hn0 : n = 0
    obtain hneq := (h n).1 hn0
    obtain hneq | hneq := hneq
    rw [hneq, hn0]
    simp [feq1]
    rw [hm0] at hmeq
    rw [hn0, hmeq] at hneq
    linarith
    have nge1 : n ≥ 1 := by 
      omega
    obtain hneq := (h n).2 nge1
    rw [hneq]
    simp [feq1]
    rw [hm0] at hmeq
    simp [hm0, hmeq]
    by_cases hn0 : n = 0
    rw [hn0, hmeq, feq1]
    have nge1 : n ≥ 1 := by omega
    obtain hneq := (h n).2 nge1
    simp [hneq, feq1]
    have mge1 : m ≥ 1 := by omega
    obtain hmeq := (h m).2 mge1
    have ineq : m ! ≥ 1 := by 
      linarith [Nat.factorial_pos m]
    obtain hmeq1 := (h (m !)).2 ineq
    rw [hmeq1, hmeq]
    by_cases hn0 : n = 0
    obtain hneq := (h n).1 hn0 
    obtain hneq | hneq := hneq
    rw [hneq, hn0]
    simp
    rw [hneq, hn0]
    have nge1 : n ≥ 1 := by omega
    obtain hneq := (h n).2 nge1
    rw [hneq]