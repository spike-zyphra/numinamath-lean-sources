import Mathlib

/- (Cauchy)

Find all functions $f: \mathbb{Q} \mapsto \mathbb{Q}$ such that for all $x, y \in \mathbb{Q}$,


$$

f(x+y)=f(x)+f(y)

$$
 -/
open Rat
theorem algebra_127452 (f : ℚ → ℚ) : (∀ x y, f (x + y) = f x + f y) ↔
    ∃ c, ∀ x, f x = c * x := by
  constructor
  -- the left direction is trivial, let's solve it first
  rotate_left
  · intro h
    obtain ⟨c, hc⟩ := h
    intro x y
    rw [hc (x+y), hc x, hc y]
    ring_nf
  · intro h
    -- we know c = f(1)
    use f 1
    intro x
    -- let's prove that f(0) = 0
    have hf0: f 0 = 0 := by
      specialize h 0 0
      simp at h; assumption
    -- now let's prove we can multiply by a natural number
    have hprod:∀d:ℕ, ∀ q:ℚ, f (d * q) = d * f q := by
      intro d q
      have hd: d = 0 ∨ 0 < d := by exact Nat.eq_zero_or_pos d
      cases' hd with hd hd
      · rw [hd]; simp; assumption
      induction d, hd using Nat.le_induction
      case base => simp
      case succ d' hd' ih =>
        specialize h (d' * q) q
        rw [Nat.cast_add, add_mul, Nat.cast_one, one_mul, h, ih]; ring_nf

    -- and Z
    have hprod:∀d:ℤ, ∀ q:ℚ, f (d * q) = d * f q := by
      intro d q
      have hd: d < 0 ∨ d = 0 ∨ 0 < d := by exact Int.lt_trichotomy d 0
      cases' hd with hd hd
      · have hn: ∃n:ℕ, d = -n := by refine Int.exists_eq_neg_ofNat ?_; linarith
        obtain ⟨n, hn⟩ := hn
        rw [hn]
        calc f (↑(-↑n) * q)
        _ = f (n * -q) := by simp
        _ = n * f (-q) := by rw [hprod]
        _ = - n * f q := by have h':= h q (-q); simp at h'; rw [hf0] at h'; have h'':f (-q)=- (f q) := (by linarith); rw [h'']; simp
      cases' hd with hd hd
      · rw [hd]; simp; assumption
      · have hn: ∃n:ℕ, d = n := by refine Int.eq_ofNat_of_zero_le ?_; linarith
        obtain ⟨n, hn⟩ := hn
        rw [hn]
        simp; rw [hprod]

    -- now we can complete
    calc f x
    _ = f (x.num /. x.den) := by simp
    _ = f (x.num * (1 /. x.den)) := by apply congr_arg; rw [← divInt_mul_divInt_cancel (x:=1) (by norm_num)]; simp;
    _ = x.num * f (1 /. x.den) := by rw [hprod]
    _ = f 1 * x := by
      specialize hprod x.den (1 /. x.den)
      conv_lhs at hprod =>
        rhs
        rw [← divInt_one, divInt_mul_divInt_cancel (by norm_num)]; simp
      rw [hprod]
      conv_rhs =>
        rw [mul_comm, ← mul_assoc]
      suffices ↑x.num = x * ↑↑x.den by rw [this]; simp
      simp