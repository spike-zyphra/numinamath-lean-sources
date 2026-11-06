import Mathlib

open Finset

def σ (k : ℕ) := ∑ d in k.divisors, d

theorem number_theory_638117 {N : ℕ} (hN : N > 0) :
  (Even N → ∑ d ∈ (N.divisors.filter Even), d = 2 * σ (N / 2)) ∧
  (Odd N → ∑ d ∈ (N.divisors.filter Even), d = 0) := by 
  constructor
  -- the case N is Even 
  · 
    intro h
    let f : ℕ → ℕ := fun n => 2 * n
    have seteq : filter Even N.divisors = 
      image f (N / 2).divisors := by 
      refine Finset.ext_iff.mpr ?_
      intro x
      constructor
      · intro hx
        simp at hx
        simp
        obtain ⟨hx1, x2, hx2⟩ := hx
        use x2
        constructor
        obtain ⟨hx0, hx1⟩ := hx1
        constructor
        · refine Nat.dvd_div_of_mul_dvd ?_
          have aux : 2 * x2 = x := by 
            rw [hx2]
            ring
          rw [aux]
          exact hx0
        · by_contra hc
          simp at hc
          interval_cases N 
          -- only possible N is 1, which is not Even
          obtain ⟨k, hk⟩ := h
          omega
        · unfold f
          rw [hx2]
          ring
      · 
        intro hx
        simp at hx ⊢
        obtain ⟨a, ha1, ha3⟩ := hx
        obtain ⟨ha1, ha2⟩ := ha1
        constructor
        constructor
        · have dvd1 : 2 * a ∣ N := by 
            refine (Nat.dvd_div_iff_mul_dvd ?_).mp ha1
            exact even_iff_two_dvd.mp h
          unfold f at ha3
          rw [← ha3]
          exact dvd1
        · linarith
        · unfold f at ha3
          rw [←ha3]
          simp
    have h1 : ∑ d ∈ filter Even N.divisors, d =
      ∑ d ∈ image f (N / 2).divisors, d := by 
      exact congrFun (congrArg Finset.sum seteq) fun d => d
    rw [h1]
    have h2 : ∑ d ∈ image f (N / 2).divisors, d = 
      ∑ d ∈ (N / 2).divisors, f d := by 
      refine sum_image ?_
      intro x hx y hy hxy
      unfold f at hxy
      linarith
    rw [h2]
    have h3 : ∑ d ∈ (N / 2).divisors, f d = 2 * ∑ d ∈ (N / 2).divisors, d := by
      exact Eq.symm (mul_sum (N / 2).divisors (fun i => i) 2)
    rw [h3]
    unfold σ
    rfl
  -- the case N is Odd
  · intro h
    -- the set (N.divisors.filter Even) is ∅ 
    have empty1 : Finset.filter Even N.divisors = ∅ := by 
      refine filter_eq_empty_iff.mpr ?_
      intro x hx
      by_contra hc
      have dvd2 : 2 ∣ x := by 
        exact even_iff_two_dvd.mp hc
      simp at hx
      obtain ⟨hx1, hx2⟩ := hx
      obtain dvd3 := dvd_trans dvd2 hx1
      obtain ⟨k, hk⟩ := h
      rw [hk] at dvd3
      omega
    rw [empty1]
    simp