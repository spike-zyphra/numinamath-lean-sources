import Mathlib
set_option maxHeartbeats 0

open Nat

/-Given a prime number  $p$ . It is known that for each integer  $a$  such that  $1<a<p/2$  there exist integer  $b$  such that  $p/2<b<p$  and  $p|ab-1$ . Find all such  $p$ .-/
theorem number_theory_8497 (p : ℕ) [hp : Fact (Nat.Prime p)]
(h : ∀ a : ℕ, 1 < a ∧ a ≤ p / 2 →
∃ b : ℕ, p / 2 < b ∧ b < p ∧ p ∣ a * b - 1) :
p < 80 := by
-- Prove by contradiction
  by_contra h'; push_neg at h'
-- Prepare some simple facts for later use
  have h'p := hp.1
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p ∣ (p - 1) * (p - 1) - 1 := by
    use p - 2; rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_sub, Nat.mul_sub]; simp
    rw [Nat.sub_sub, Nat.sub_one_add_one, Nat.sub_sub, mul_two]; assumption
  have h'p0 : NeZero p := by rw [neZero_iff]; assumption
  have odp : Odd p := by
    apply Prime.odd_of_ne_two; assumption; linarith
  rcases odp with ⟨k, hk0⟩
  have hk1 : 40 ≤ k := by
    by_contra h'k1; push_neg at h'k1; linarith
  have pcpi: ∀ i, i ∈ Finset.Icc 2 k → Nat.Coprime i p := by
    intro i hi; simp at hi; rcases hi with ⟨hil, hir⟩
    rw [Nat.coprime_comm]; apply Nat.coprime_of_lt_prime; linarith
    rw [hk0]; linarith; assumption

-- Define the inverse function $f$ for any $a$ between $2$ and $p/2$
  let f (a : ℕ) : ℕ := if ha : a ∈ Finset.Icc 2 k then (ZMod.unitOfCoprime a (pcpi a ha))⁻¹.val.val else 0

-- Prove the key property of the function $f$ that $y=f(x)$ if and only if $p$ divides $x*y-1$
  have hf0 : ∀ x y, x ∈ Finset.Icc 2 k → 1 ≤ y ∧ y < p → ( f x = y ↔ p ∣ x * y - 1 ) := by
    intro x y hx hy; simp at hx
    have hx0 : (x : ZMod p) ≠ 0 := by
      intro hxne; rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at hxne
      apply le_of_dvd at hxne; linarith; linarith
    constructor
    · intro hxy; simp [f] at hxy; split_ifs at hxy
      · rw [← ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.cast_sub, sub_eq_zero]
        simp; rw [mul_comm, mul_eq_one_iff_eq_inv₀ hx0, ← hxy]; simp
        apply one_le_mul; linarith; by_contra hy; simp at hy
        rw [hy] at hxy; simp at hxy; contradiction
    intro h'xy; simp [f]; split_ifs
    · rw [← ZMod.val_cast_of_lt hy.right]; congr
      symm; rw [← mul_eq_one_iff_eq_inv₀ hx0, mul_comm]
      rw [← ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.cast_sub] at h'xy
      rw [sub_eq_zero] at h'xy; simp at h'xy; assumption
      apply one_le_mul; linarith; exact hy.left

-- Prove that $f$ is injective on the set of natural numbers between $2$ and $k$
  have hf1 : Set.InjOn f (Finset.Icc 2 k) := by
    rw [Set.InjOn]; intro x1 hx1 x2 hx2 h12; simp at hx1; simp at hx2
    simp [f] at h12; split_ifs at h12; apply ZMod.val_injective at h12
    simp at h12; rw [ZMod.natCast_eq_natCast_iff'] at h12
    have h'x1 : x1 % p = x1 := by apply Nat.mod_eq_of_lt; linarith
    have h'x2 : x2 % p = x2 := by apply Nat.mod_eq_of_lt; linarith
    rw [← h'x1, ← h'x2]; assumption

-- Prove that $f(a)$ is between $k+1$ and $p-2$
  have hf2a : f '' (Finset.Icc 2 k) ⊆ Finset.Icc (k+1) (p-2) := by
    intro y; simp; intro x hx0 hx1 hx2
    simp [f] at hx2; split_ifs at hx2
    · have h'x1 : 1 < x ∧ x ≤ p / 2 := by
        constructor
        · linarith
        rw [Nat.le_div_iff_mul_le]; rw [hk0]
        have : x * 2 ≤ k * 2 := by linarith
        linarith; norm_num
      rcases h x h'x1 with ⟨z, hz1, hz2, hz3⟩
      rw [← ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.cast_sub, sub_eq_zero] at hz3
      simp at hz3; rw [mul_comm, mul_eq_one_iff_eq_inv₀] at hz3
      rw [← hz3] at hx2; simp at hx2; rw [Nat.mod_eq_of_lt hz2] at hx2
      rw [← hx2]; constructor
      · rw [Nat.div_lt_iff_lt_mul, hk0, Nat.lt_iff_add_one_le] at hz1
        rw [mul_comm, add_assoc, show 1+1=1*2 by simp, ← add_mul] at hz1
        simp at hz1; assumption; norm_num
      rw [Nat.lt_iff_add_one_le, ← Nat.le_sub_iff_add_le, Nat.le_iff_lt_or_eq] at hz2
      rcases hz2 with hz2l | hz2r
      · rw [Nat.lt_iff_add_one_le, ← Nat.le_sub_iff_add_le, Nat.sub_sub] at hz2l
        simp at hz2l; assumption; rw [Nat.le_sub_iff_add_le]; simp; linarith
        linarith
      rw [← ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.cast_sub, sub_eq_zero] at hp1
      simp at hp1; rw [← hz2r, mul_eq_one_iff_eq_inv₀] at hp1
      rw [hp1] at hz3; simp at hz3; rw [hz2r, ZMod.natCast_eq_natCast_iff'] at hz3
      have : (p - 1) % p = p - 1 := by
        apply Nat.mod_eq_of_lt; simp; linarith
      rw [this] at hz3
      have : x % p = x := by apply Nat.mod_eq_of_lt; linarith
      rw [this] at hz3; rw [← hz3] at h'x1; linarith
      intro hnz; rw [hnz] at hp1; simp at hp1
      apply one_le_mul; rw [Nat.le_sub_iff_add_le]; simp; linarith; linarith
      rw [Nat.le_sub_iff_add_le]; simp; linarith; linarith; linarith
      intro hnx; rw [hnx] at hz3; simp at hz3
      apply one_le_mul; linarith; linarith
    have : 2 ≤ x ∧ x ≤ k := ⟨hx0, hx1⟩
    contradiction

  have hf2 : f '' (Finset.Icc 2 k) = Finset.Icc (k+1) (p-2) := by
    apply Set.eq_of_subset_of_ncard_le hf2a
    rw [Set.ncard_image_of_injOn, Set.ncard_coe_Finset, Set.ncard_coe_Finset]
    simp; rw [add_assoc, ← Nat.sub_add_comm, ← add_assoc, ← two_mul]
    rw [Nat.add_sub_assoc, show 2-1=1 by simp, hk0]; simp
    linarith; assumption

  rw [Set.ext_iff] at hf2; simp at hf2
-- Check some special values of $f$
  have hf3 : f 2 = k + 1 := by
    rw [hf0 2 (k+1), mul_add, mul_one]; simp; rw [← hk0]; simp
    linarith; constructor
    · linarith
    linarith

  have hf4 : f k = p - 2 := by
    rw [hf0 k (p-2), Nat.mul_sub, Nat.sub_sub]
    nth_rw 2 [mul_comm]; rw [← hk0]
    use k-1; rw [Nat.mul_sub, mul_comm]; simp
    simp; linarith; constructor
    · rw [Nat.le_sub_iff_add_le]; linarith; linarith
    simp; linarith

-- Two key observations about the function $f$
  have hf5 : ∀ x, f x ≠ x + 1 := by
    intro x hx0
    have h'x0 := hx0
    simp [f] at hx0; split_ifs at hx0; rename_i hx1
    have hx2 : k + 1 ≤ x + 1 ∧ x + 1 ≤ p - 2 := by apply (hf2 (x+1)).mp; use x
    simp at hx2
    have hx3 : x = k := by linarith
    rw [hx3, hf4, hk0] at h'x0; simp at h'x0
    rw [show 2=1+1 by simp, add_mul, one_mul] at h'x0; linarith

  have hf6 : ∀ x, f x ≠ x + 2 := by
    intro x hx0
    have h'x0 := hx0
    simp [f] at hx0; split_ifs at hx0; rename_i hx1
    have hx2 : k + 1 ≤ x + 2 ∧ x + 2 ≤ p - 2 := by apply (hf2 (x+2)).mp; use x
    rcases hx2 with ⟨hx2l, _⟩; simp at hx2l
    rcases hx1 with ⟨_, hx1r⟩; rw [Nat.le_iff_lt_or_eq] at hx1r
    rcases hx1r with hx1rr | hx1rl
    · rw [Nat.lt_iff_add_one_le] at hx1rr
      have h''x : x + 1 = k := by linarith
      symm at h''x; rw [← Nat.sub_eq_iff_eq_add] at h''x
      rw [← h''x, ← Nat.sub_add_comm, Nat.add_sub_assoc] at h'x0; simp at h'x0
      have : 2 = k - 1 := by
        apply hf1; simp; linarith; simp; rw [Nat.le_sub_iff_add_le]
        simp; linarith; linarith; linarith
      symm at this; linarith; linarith; linarith; linarith
    rw [hx1rl] at h'x0
    have : p - 2 = k + 2 := by linarith
    rw [hk0] at this; simp at this; linarith

-- If $2$ is a square modulo $p$, we will be able to construct $A$ such that $f(A)$ equals $A+2$, which is a contradiction
  have two_ne_sq_modp : ¬ IsSquare (2 : ZMod p) := by
    intro sq2; rcases sq2 with ⟨a, h'a⟩; let ha := h'a
    let a' := a - 1
    have ha' : a = a' + 1 := by simp [a']
    rw [ha', mul_add, add_mul, mul_one, one_mul, add_assoc] at ha
    nth_rw 2 [← add_assoc] at ha; rw [← two_mul, ← add_assoc] at ha
    rw [← add_mul, mul_comm, ← sub_eq_iff_eq_add] at ha
    nth_rw 1 [← mul_one 2] at ha; rw [two_mul] at ha; simp at ha
    let A := a'.val
    have hA0 : A = a' := by simp [A]
    have hA1 : A < p := by simp [A]; apply ZMod.val_lt
    rw [← hA0, show (2:ZMod p) = (2:ℕ) by simp] at ha
    rw [← Nat.cast_add, ← Nat.cast_mul, show (1:ZMod p) = (1:ℕ) by simp] at ha
    rw [ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd'] at ha
    have hA2 : f A = A + 2 := by
      rw [hf0]; assumption; simp; constructor
      · by_contra h'A; push_neg at h'A; rw [Nat.lt_iff_le_pred] at h'A
        simp at h'A; rw [Nat.le_one_iff_eq_zero_or_eq_one] at h'A
        rcases h'A with h'Al | h'Ar
        · rw [h'Al] at hA0; rw [← hA0] at ha'; rw [ha'] at h'a
          simp at h'a; rw [← mul_one 2, two_mul] at h'a; simp at h'a
        rw [h'Ar] at ha; simp at ha; apply Nat.le_of_dvd at ha; linarith
        norm_num; norm_num
      by_contra hnA; push_neg at hnA; rcases le_or_gt A (p-2) with h'Al | h'Ar
      · have hA3 : ∃ x_1, (2 ≤ x_1 ∧ x_1 ≤ k) ∧ f x_1 = A := by
          rw [hf2]; constructor
          · linarith
          assumption
        rcases hA3 with ⟨x, hx0, hx1⟩;
        let h''x1 := hx1
        rw [hf0] at hx1
        by_cases hx2 : x ≤ k - 1
        · have hA4 : p ∣ A * (A + 2 - x) := by
            have : A * (A + 2 - x) = (A * (A + 2) - 1) - (x * A - 1) := by
              rw [Nat.sub_sub, Nat.add_sub_cancel']; nth_rw 3 [mul_comm]
              rw [Nat.mul_sub]; apply one_le_mul; linarith; linarith
            rw [this]; apply Nat.dvd_sub; apply Nat.sub_le_sub_right
            rw [mul_comm]; apply Nat.mul_le_mul_left; linarith
            assumption; assumption
          apply Prime.dvd_or_dvd at hA4; rcases hA4 with hA4l | hA4r
          · apply Nat.le_of_dvd at hA4l; linarith; linarith
          apply Nat.le_of_dvd at hA4r; rw [Nat.le_sub_iff_add_le] at hA4r
          linarith; linarith; rw [Nat.sub_pos_iff_lt]; linarith
          apply Nat.prime_iff.mp; assumption
        push_neg at hx2; rw [Nat.lt_iff_add_one_le, Nat.sub_one_add_one] at hx2
        have hx3 : x = k := by linarith
        rw [hx3, hf4] at h''x1; rw [← h''x1, Nat.sub_add_cancel, mul_comm] at ha
        have := Nat.dvd_sub (show p*(p-2)-1≤p*(p-2) by simp) (show p∣p*(p-2) by use p-2) ha
        rw [Nat.sub_sub_eq_min] at this; apply Nat.le_of_dvd at this
        rw [Nat.le_min] at this; linarith; rw [Nat.lt_min]; constructor
        · apply Nat.mul_pos; linarith; linarith
        norm_num; linarith; linarith; simp; assumption; constructor
        · linarith
        assumption
      rw [gt_iff_lt, Nat.lt_iff_add_one_le, show 2=1+1 by simp] at h'Ar
      rw [← Nat.sub_sub, Nat.sub_one_add_one] at h'Ar
      rw [Nat.lt_iff_add_one_le, ← Nat.le_sub_iff_add_le] at hA1
      have : A = p - 1 := by linarith
      rw [this, show 2=1+1 by simp, ← add_assoc, Nat.sub_one_add_one, mul_comm] at ha
      rw [← sq_sub_sq, Nat.sub_sub] at ha; simp at ha
      have := Nat.dvd_sub (show p^2-2≤p^2 by simp) (show p ∣ p^2 by use p; rw [pow_two]) ha
      rw [Nat.sub_sub_eq_min] at this; apply Nat.le_of_dvd at this
      rw [Nat.le_min] at this; linarith; rw [Nat.lt_min]; constructor
      · apply Nat.pow_pos; linarith
      norm_num; linarith; linarith; rw [← Nat.pos_iff_ne_zero, Nat.sub_pos_iff_lt]
      linarith; constructor
      · linarith
      by_contra hAn; push_neg at hAn; rw [Nat.le_iff_lt_or_eq] at hAn
      rcases hAn with hAnl | hAnr
      · rw [Nat.lt_iff_add_one_le] at hAnl; simp at hAnl
        rw [Nat.le_iff_lt_or_eq] at hAnl
        rcases hAnl with h'Anl | h'Anr
        · rw [Nat.lt_iff_add_one_le] at h'Anl; simp at h'Anl; linarith
        rw [← Nat.sub_eq_iff_eq_add] at h'Anr; rw [← h'Anr] at ha
        rw [show 2=1+1 by simp, ← add_assoc, Nat.sub_one_add_one, mul_comm] at ha
        rw [← sq_sub_sq, Nat.sub_sub] at ha; simp at ha
        have := Nat.dvd_sub (show p^2-2≤p^2 by simp) (show p ∣ p^2 by use p; rw [pow_two]) ha
        rw [Nat.sub_sub_eq_min] at this; apply Nat.le_of_dvd at this
        rw [Nat.le_min] at this; linarith; rw [Nat.lt_min]; constructor
        · apply Nat.pow_pos; linarith
        norm_num; linarith; linarith
      rw [← hAnr] at ha; rw [← Nat.sub_eq_iff_eq_add] at hAnr
      rw [← hAnr, mul_comm] at ha
      have := Nat.dvd_sub (show p*(p-2)-1≤p*(p-2) by simp) (show p∣p*(p-2) by use p-2) ha
      rw [Nat.sub_sub_eq_min] at this; apply Nat.le_of_dvd at this
      rw [Nat.le_min] at this; linarith; rw [Nat.lt_min]; constructor
      · apply Nat.mul_pos; linarith; rw [gt_iff_lt, Nat.sub_pos_iff_lt]; linarith
      norm_num; linarith
    have := hf6 A
    contradiction; rw [Nat.one_le_iff_ne_zero]; simp; intro h'A
    rw [h'A] at ha; simp at ha; rw [Nat.modEq_zero_iff_dvd] at ha
    apply Nat.le_of_dvd at ha; linarith; norm_num

-- If $5$ is a square modulo $p$, we will be able to construct $A$ such that $f(A)$ equals $A+1$, which is a contradiction
  have five_ne_sq_modp : ¬ IsSquare (5 : ZMod p) := by
-- Introduce variables and assumption, we define $A$ to be $((k+1)*(a-1)).val$
    intro sq5; rcases sq5 with ⟨a, h'a⟩; --let ha := h'a
    let A := ((k + 1) * (a - 1)).val
    have hA : (1 : ZMod p) + 2 * A = a := by
      simp [A]; rw [← mul_assoc]
      have : 2 * ((k: ZMod p) + 1) = ((2 * k + 1): ℕ) + 1 := by
        push_cast; ring
      rw [this, ← hk0]; simp
-- Prove $A$ is less than $p$
    have Altp : A < p := by simp [A]; apply ZMod.val_lt
-- Prove $A$ is greater or equal to $2$ by assuming $A$ equals one
-- and derive contradictions
    have Age2 : 2 ≤ A := by
      by_contra Alt; push_neg at Alt
      have Apos : 0 < A := by
        simp [A]; rw [ZMod.val_pos]
        by_contra mul0; simp at mul0
        rcases mul0 with l0|r0
        · norm_cast at l0; rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at l0
          apply Nat.le_of_dvd at l0; linarith; linarith
        rw [sub_eq_zero] at r0; simp [r0] at h'a
        rw [← sub_eq_zero] at h'a; ring_nf at h'a
        rw [show (4:ZMod p)=(4:ℕ) by rfl, ZMod.natCast_zmod_eq_zero_iff_dvd] at h'a
        apply Nat.le_of_dvd at h'a; linarith; norm_num
      have Aeq1: A = 1 := by linarith
      simp [A] at Aeq1; rw [ZMod.val_eq_one] at Aeq1
      apply_fun (λ x => 2 * x) at Aeq1
      rw [← mul_assoc, mul_one] at Aeq1; norm_cast at Aeq1
      rw [show 2*(k+1)=2*k+1+1 by ring, ← hk0] at Aeq1
      push_cast at Aeq1; simp at Aeq1; rw [sub_eq_iff_eq_add] at Aeq1
      norm_num at Aeq1; simp [Aeq1] at h'a; norm_num at h'a
      symm at h'a; rw [← sub_eq_zero] at h'a; norm_num at h'a
      rw [show (4:ZMod p)=(4:ℕ) by rfl, ZMod.natCast_zmod_eq_zero_iff_dvd] at h'a
      apply Nat.le_of_dvd at h'a; linarith; norm_num; linarith
-- Prove that $p$ divides $A*(A+1)-1$
    have pdA : p ∣ A * (A + 1) - 1 := by
-- Rewrite the division relation in ZMod by applying ZMod.natCast_zmod_eq_zero_iff_dvd
      rw [← ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.cast_sub]
-- Simplify type conversions
      rw [sub_eq_zero]; push_cast; ring_nf
-- Prove that $4$ is invertible modulo $p$
      have inv4 : Invertible (4:ZMod p) := by
        use ((k:ZMod p)+1)^2; rw [show (4:ZMod p)=2^2 by norm_num]
        have : ((k:ZMod p)+1)*2=(((2*k+1):ℕ):ZMod p)+1 := by norm_cast; ring_nf
        rw [← mul_pow, this, ← hk0]; simp
        rw [mul_comm]; rw [show (4:ZMod p)=2^2 by norm_num]
        have : ((k:ZMod p)+1)*2=(((2*k+1):ℕ):ZMod p)+1 := by norm_cast; ring_nf
        rw [← mul_pow, this, ← hk0]; simp
-- Rewrite the final goal and prove it
      rw [← mul_right_inj_of_invertible (4:ZMod p), ← add_right_inj (1:ZMod p)]
      ring_nf; rw [show 1+↑A*4+↑A^2*4=(1+2*(A:ZMod p))^2 by ring]
      rw [hA, pow_two]; symm; assumption
      apply one_le_mul; linarith; linarith
-- Prove $A$ is less or equal to $k$ by assuming it is greater than $k$
-- then apply hf2 to find some $x$ such that $f(x)$ equals $A$
    have Alek : A ≤ k := by
      by_contra Agtk; push_neg at Agtk
      replace Agtk : k + 1 ≤ A := by linarith
-- Prove that $A$ can not be $p-1$ because if not,
-- we will have $p$ divides $p*(p-1)-1$, which is absurd
      by_cases Aeqs1 : p - 2 < A
      · replace Aeqs1 : A = p - 1 := by
          have : A ≤ p - 1 := by
            rw [Nat.lt_iff_le_pred] at Altp; assumption
            linarith
          have : p - 1 ≤ A := by
            rw [Nat.lt_iff_add_one_le] at Aeqs1; zify at Aeqs1
            rw [Nat.cast_sub] at Aeqs1; ring_nf at Aeqs1
            rw [neg_add_eq_sub, show (1:ℤ)=(1:ℕ) by rfl, ← Nat.cast_sub] at Aeqs1
            rw [cast_le] at Aeqs1; assumption
            all_goals linarith
          linarith
        rw [Aeqs1, Nat.sub_add_cancel] at pdA
        have : p ∣ ((p - 1) * p - 1) + 1 := by
          rw [Nat.sub_add_cancel]; apply Nat.dvd_mul_left
          apply one_le_mul; linarith; linarith
        rw [← Nat.dvd_add_iff_right] at this
        simp at this; linarith; assumption; linarith
      push_neg at Aeqs1
-- Apply hf2 to get an $x$ between $2$ and $k$ such that $f(x)=A$
      have : ∃ x_1, (2 ≤ x_1 ∧ x_1 ≤ k) ∧ f x_1 = A := by
        rw [hf2]; constructor; assumption; assumption
      rcases this with ⟨x,⟨hx1,hx2⟩⟩
-- Apply lemma hf0 at the equality $f(x)=A$, we get a division relation
      rw [hf0, mul_comm] at hx2
-- Compare this division relation with pdA, prove that $p$ divides the following difference
      apply Nat.dvd_sub at pdA; replace pdA := pdA hx2
-- Simplify the assumptions and write the RHS as a product
      rw [Nat.sub_sub_sub_cancel_right, ← Nat.mul_sub] at pdA
-- Since $p$ is a prime, it has to divide one of the two factors
-- in each case, we can derive contradiction easily
      rw [Nat.Prime.dvd_mul] at pdA; rcases pdA with pdA|pdA
      · apply Nat.le_of_dvd at pdA; linarith; linarith
      apply Nat.le_of_dvd at pdA
      have : A + 1 - x ≤ A + 1 := by apply Nat.sub_le
      apply Nat.add_le_add_right at Aeqs1
      replace Aeqs1 := Aeqs1 1
      rw [show 2=1+1 by norm_num, ← Nat.sub_sub, Nat.sub_add_cancel] at Aeqs1
      have : p - 1 < p := by apply Nat.sub_one_lt; linarith
      linarith; rw [Nat.le_sub_iff_add_le]; linarith; linarith
      rw [Nat.sub_pos_iff_lt]; linarith; assumption
      apply one_le_mul; linarith; linarith
      rw [Nat.sub_le_sub_iff_right, mul_le_mul_iff_of_pos_left]
      linarith; linarith
      apply one_le_mul; linarith; linarith
      simp; assumption; constructor; linarith; assumption
-- Now we have proved that $A$ is less or equal to $k$, we can then apply
-- lemma hf0 to show that $f(A)$ is equal to $A+1$
    have : f A = A + 1 := by
      rw [hf0]; assumption; simp
      constructor; assumption; assumption
      constructor; linarith; linarith
-- But by the lemma hf5, we have $f(A)$ is not equal to $A+1$, which is a contradiction
    have := hf5 A; contradiction

-- Apply the famous law of quadratic reciprocity, we can get division relations on $p$
  have p_cgr : (5 ∣ p - 2 ∨ 5 ∣ p - 3) ∧ (8 ∣ p - 3 ∨ 8 ∣ p - 5) := by
-- Prove that $2$ and $5$ are prime
    have r0 : Fact (Nat.Prime 5) := by rw [fact_iff]; norm_num
-- Rewrite the two above propositions in terms of Legendre symbol and apply the law of quadratic reciprocity
    have r1 : legendreSym 5 p = -1 := by
      rw [legendreSym.quadratic_reciprocity']; simp; rw [legendreSym.eq_neg_one_iff]
      have : (5 : ZMod p) = (5 : ℤ) := by simp
      rw [← this]; assumption; linarith; norm_num
    have r2 : legendreSym p 2 = -1 := by
      rw [legendreSym.eq_neg_one_iff]
      have : (2 : ZMod p) = (2 : ℤ) := by simp
      rw [← this]; assumption
    constructor
-- Case to case study on proving $5$ divides $p-2$ or $p-3$
    · have hpmod5 := Nat.mod_add_div p 5
      rw [legendreSym.eq_neg_one_iff'] at r1
      have h'pmod5 : p % 5 ≤ 4 := by
        rw [show 4=Nat.pred 5 by norm_num, Nat.le_pred_iff_lt]
        apply Nat.mod_lt; norm_num; norm_num
      rw [Nat.le_iff_lt_or_eq] at h'pmod5; rcases h'pmod5 with h1l | h1r
      · rw [Nat.lt_iff_le_pred, Nat.le_iff_lt_or_eq] at h1l; simp at h1l
        rcases h1l with h2l | h2r
        · rw [Nat.lt_iff_le_pred, Nat.le_iff_lt_or_eq] at h2l; simp at h2l
          rcases h2l with h3l | h3r
          · rw [Nat.lt_iff_le_pred, Nat.le_iff_lt_or_eq] at h3l; simp at h3l
            rcases h3l with h4l | h4r
            · rw [h4l] at hpmod5; simp at hpmod5
              have : 5 ∣ p := by use p/5; symm; assumption
              rw [Nat.prime_dvd_prime_iff_eq] at this; linarith
              norm_num; assumption
            have : IsSquare (p : ZMod 5) := by
              rw [show (p : ZMod 5)=(p:ℤ) by rfl]
              apply ZMod.isSquare_of_jacobiSym_eq_one
              rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff']
              use 1; simp; rw [ZMod.natCast_eq_iff]; use p/5; rw [h4r] at hpmod5
              rw [ZMod.val_one]; symm; assumption
              by_contra h5; rw [ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.prime_dvd_prime_iff_eq] at h5
              linarith; norm_num; assumption
            contradiction; norm_num
          left; use p/5; rw [Nat.sub_eq_iff_eq_add, add_comm]; symm
          rw [h3r] at hpmod5; assumption; linarith; norm_num
        right; use p/5; rw [Nat.sub_eq_iff_eq_add, add_comm]; symm
        rw [h2r] at hpmod5; assumption; linarith; norm_num
      have : IsSquare (p : ZMod 5) := by
        rw [show (p : ZMod 5)=(p:ℤ) by rfl]
        apply ZMod.isSquare_of_jacobiSym_eq_one
        rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff']
        use 2; rw [ZMod.natCast_eq_iff]; use p/5; rw [h1r] at hpmod5
        rw [two_mul, ZMod.val_add, ← one_add_one_eq_two, ZMod.val_add, ZMod.val_one]
        simp; symm; assumption
        by_contra h5; rw [ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.prime_dvd_prime_iff_eq] at h5
        linarith; norm_num; assumption
      contradiction
-- Prove that $p$ equals $3$ or $5$ modulo $8$ by applying the second supplement law of quadratic reciprocity
    have : ¬ (Fintype.card (ZMod p) % 8 ≠ 3 ∧ Fintype.card (ZMod p) % 8 ≠ 5) := by
      rw [← FiniteField.isSquare_two_iff]; assumption
    push_neg at this; simp at this
    have hpmod8 := Nat.mod_add_div p 8
    by_cases h' : p % 8 = 3
    · left; use p/8; rw [Nat.sub_eq_iff_eq_add, add_comm]; symm
      rw [h'] at hpmod8; assumption; linarith
    replace h' := this h'; right; use p/8
    rw [Nat.sub_eq_iff_eq_add, add_comm]; symm
    rw [h'] at hpmod8; assumption; linarith
                        
-- Prove by cases, in each case we will deduct some contradictions
  rcases p_cgr with ⟨p_cgr1, p_cgr2⟩; rcases p_cgr1 with p_cgr1l | p_cgr1r
-- Case $p≡2(Mod 5)$, we we will first use division relations to find out the value of $f(5)$
  · rcases p_cgr1l with ⟨w, hw0⟩
    have hw1 : f 5 = 2 * w + 1 := by
      rw [hf0, mul_add, mul_comm, mul_assoc]; rw [mul_comm] at hw0
      rw [← hw0, Nat.mul_sub]; simp; rw [Nat.sub_add_cancel]; simp
      linarith; simp; linarith; constructor
      · simp
      by_contra hnw; push_neg at hnw
      rw [Nat.sub_eq_iff_eq_add] at hw0; linarith; linarith
-- use the fact that $f(5)$ is greater or equal to $k+1$ to deduct a contradiction
    have hw2 : k + 1 ≤ 2 * w + 1 ∧ 2 * w + 1 ≤ p - 2 := by
      apply (hf2 (2*w+1)).mp; use 5; constructor
      · constructor
        · norm_num
        linarith
      assumption
    rcases hw2 with ⟨hw2l, _⟩
    rw [hk0] at hw0; simp at hw0 ; rw [Nat.sub_eq_iff_eq_add] at hw0
    have := Nat.add_le_add hw2l hw2l
    ring_nf at this; rw [mul_comm, hw0, add_comm, add_assoc] at this
    linarith; linarith
-- Case $p≡3(Mod 5)$, split to cases when $p≡3(Mod 8)$ and $p≡5(Mod 8)$
  rcases p_cgr2 with p_cgr2l | p_cgr2r
-- Case $p≡3(Mod 8)$, we will first use division relations to find out the value of $f(40)$
  · have hp2 : 40 ∣ 13 * p + 1 := by
      rw [show 40=Nat.lcm 5 8 by norm_num]; apply Nat.lcm_dvd
      · rcases p_cgr1r with ⟨s,hs⟩
        rw [Nat.sub_eq_iff_eq_add] at hs; use 13*s+8
        rw [hs]; ring; linarith
      rcases p_cgr2l with ⟨s', hs'⟩
      rw [Nat.sub_eq_iff_eq_add] at hs'; use 13*s'+5
      rw [hs']; ring; linarith
    rcases hp2 with ⟨u, hu0⟩
    have hu1 : f 40 = u := by
      rw [hf0]; rw [← hu0]; simp
      simp; assumption; constructor
      · by_contra hnu; simp at hnu
        rw [hnu] at hu0; linarith
      by_contra h'nu; push_neg at h'nu
      apply Nat.mul_le_mul_left 40 at h'nu; linarith
-- Then we use the fact that $f(40)$ is greater or equal to $k+1$ to deduct a contradiction
    have hu2 : k + 1 ≤ u ∧ u ≤ p - 2 := by
      apply (hf2 u).mp; use 40; constructor
      · constructor
        · norm_num
        assumption
      assumption
    linarith
-- Case $p≡5(Mod 8)$, we will first use division relations to find out the value of $f(40)$
  have hp3 : 40 ∣ 3 * p + 1 := by
    rw [show 40=Nat.lcm 5 8 by norm_num]; apply Nat.lcm_dvd
    · rcases p_cgr1r with ⟨s,hs⟩
      rw [Nat.sub_eq_iff_eq_add] at hs
      use 3*s+2; rw [hs]; ring; linarith
    rcases p_cgr2r with ⟨s', hs'⟩
    rw [Nat.sub_eq_iff_eq_add] at hs'
    use 3*s'+2; rw [hs']; ring; linarith
  rcases hp3 with ⟨v, hv0⟩
  have hv1 : f 40 = v := by
    rw [hf0, ← hv0]; simp; simp; assumption; constructor
    · by_contra hnv; simp at hnv; linarith
    by_contra hnv; push_neg at hnv; linarith
-- Then we use the fact that $f(40)$ is greater or equal to $k+1$ to deduct a contradiction
  have hv2 : k + 1 ≤ v ∧ v ≤ p - 2 := by
      apply (hf2 v).mp; use 40; constructor
      · constructor
        · norm_num
        assumption
      assumption
  rcases hv2 with ⟨hv2l, _⟩
  apply Nat.mul_le_mul_left 40 at hv2l; linarith