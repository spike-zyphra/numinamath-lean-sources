import Mathlib

/-Let $\mathbb{Z}$ be the set of integers. Find all functions  $f: \mathbb{Z}\rightarrow \mathbb{Z}$  such that, for any two integers  $m, n$ ,    $$ f(m^2)+f(mf(n))=f(m+n)f(m). $$  *Proposed by Victor Domínguez and Pablo Valeriano*-/
theorem number_theory_8633 (f : ℤ → ℤ)
(hf : ∀ m n : ℤ, f (m ^ 2) + f (m * f (n)) = f (m + n) * f m) :
(∀ k, f k = 0) ∨ (∀ k, f k = 2) ∨ (∀ k, f k = k) := by
-- Prove by cases
  by_cases h0 : f 0 ≠ 0
-- If $f(0)≠0$, prove that $f(k)=2$
  have r1 := hf 0
  ring_nf at r1; simp at r1
  right; left; intro k
  cases r1 k with
  | inl h => symm; assumption
  | inr h => contradiction

-- If $f(0)=0$, prove that $f(k)=0$ or $f(k)=k$
  push_neg at h0
-- First prove that $f$ is either even or odd
  have t1 : ∀ m, f (m ^ 2) = f m * f m := by
    intro m
    have := hf m 0
    rw [h0] at this; simp at this; rw [h0] at this; simp at this
    assumption
  have r1 : ∀ m, f m = f (-m) ∨ f m = -f (-m) := by
    intro m
    have t2 := hf (-m) 0
    rw [h0] at t2; simp at t2; rw [h0] at t2; simp at t2
    rw [t1, ← pow_two, ← pow_two, sq_eq_sq_iff_eq_or_eq_neg] at t2
    assumption
-- Prove that $f(1)$ is either $1$ or $0$
  have r3 := hf 1 0
  simp at r3; rw [h0] at r3; rw [h0, ← pow_two] at r3; simp at r3
  symm at r3; apply eq_zero_or_one_of_sq_eq_self at r3
  have r4 : ∀ m, f (m ^ 2) + f (m * f 1) = f (m + 1) * f m := by
    intro m; exact hf m 1
-- Prove by cases
  cases r3 with
-- If $f(1)=0$, prove that $f(k)=0$
  | inl hll => left; intro k
               rw [hll] at r4; simp at r4
               rw [h0] at r4; simp at r4
               have r5 : ∀ m, f (m + 1) = f m ∨ f m = 0 := by
                 intro m
                 have q1 := t1 m
                 have q2 := r4 m
                 rw [q2] at q1; simp at q1; assumption
-- If $a$ is a natural number, prove that $f(a)=0$ by induction
               have v1 : ∀ a : ℕ, f (Int.ofNat a) = 0 := by
                 intro a; induction a with
                 | zero => simp; assumption
                 | succ i ih => simp; simp at ih
                                by_contra hne; push_neg at hne
                                have r6 : ∀ j : ℕ, f ((i:ℤ) + 1 + j) = f ((i:ℤ) + 1) := by
                                  intro j; induction j with
                                  | zero => simp
                                  | succ n ih => cases r5 ((i:ℤ)+1+n) with
                                                 | inl hzz => rw [ih] at hzz; assumption
                                                 | inr hyy => rw [ih] at hyy; contradiction
                                have r7 := t1 (i+1)
                                have r8 := r6 (i^2+i)
                                have : (i:ℤ) + 1  + ↑(i ^ 2 + i) = (↑i + 1) ^ 2 := by
                                  ring_nf; simp; ring
                                rw [this, r7, ← pow_two] at r8
                                apply eq_zero_or_one_of_sq_eq_self at r8
                                cases r8 with
                                | inl h' => contradiction
                                | inr h' => rw [h'] at r6; rw [h'] at r7; simp at r7
                                            have := hf ((i:ℤ)+1) ((i:ℤ)+1)
                                            rw [h'] at this; simp at this
                                            rw [h', r7] at this
                                            have u1 := r6 (i+1)
                                            have u2 : ↑(i+1) = (i:ℤ)+1 := by rfl
                                            rw [u2] at u1; rw [u1] at this
                                            contradiction
-- Prove the general case by induction
               induction k with
               | ofNat a => exact v1 a
               | negSucc b => rw [Int.negSucc_eq]
                              cases r1 ((b : ℤ)+1) with
                              | inl h'' => have := v1 (b+1)
                                           have w1 : Int.ofNat (b + 1) = ↑b + 1 := rfl
                                           rw [w1] at this; rw [this] at h''
                                           symm; assumption
                              | inr h'' => have := v1 (b+1)
                                           have w1 : Int.ofNat (b + 1) = ↑b + 1 := rfl
                                           rw [w1] at this; symm at h''
                                           rw [this, Int.neg_eq_zero] at h''; assumption
-- If $f(1)=1$, prove that $f(k)=k$
  | inr hrr => right; right; intro k; rw [hrr] at r4; simp at r4
               have o1 : ∀ m, 1 + f m = f (m + 1) ∨ f m = 0 := by
                 intro m
                 have := r4 m
                 rw [t1 m, add_comm] at this
                 nth_rw 1 [← one_mul (f m)] at this
                 rw [← add_mul] at this; simp at this; assumption
-- If $a$ is a natural number, prove that $f(a)=a$ by induction
               have v2 : ∀ a : ℕ, f (Int.ofNat a) = a := by
                 intro a; induction a with
                 | zero => simp; assumption
                 | succ n ih => simp; simp at ih
                                cases o1 (n:ℤ) with
                                | inl hss => rw [ih, add_comm] at hss; symm; assumption
                                | inr hxx => rw [ih] at hxx; rw [hxx]; simp; assumption
-- Prove the general case by induction
               induction k with
               | ofNat a => exact v2 a
               | negSucc b => rw [Int.negSucc_eq]
                              cases r1 ((b : ℤ)+1) with
                              | inl h'' => have := v2 (b+1)
                                           have w1 : Int.ofNat (b + 1) = ↑b + 1 := rfl
                                           rw [w1] at this; rw [this] at h''
                                           have o2 := hf ((b : ℤ)+1) (-((b : ℤ)+1))
                                           have o3 : (b : ℤ) + 1 = ↑(b + 1) := rfl
                                           rw [← h'', o3] at o2; ring_nf at o2
                                           rw [h0] at o2; simp at o2
                                           have o4 := v2 ((1+b)^2)
                                           simp at o4; rw [o2] at o4; symm at o4
                                           apply sq_eq_zero_iff.mp at o4; linarith
                              | inr h'' => have := v2 (b+1)
                                           have w1 : Int.ofNat (b + 1) = ↑b + 1 := rfl
                                           rw [w1] at this; symm at h''
                                           rw [Int.neg_eq_comm] at h''
                                           rw [← h'', this]; simp