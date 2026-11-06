import Mathlib

open Relation Pointwise

/- One movement: the positions of the mathematician on the ladder.
  The mathematician can move from rung `x` to rung `y` in two ways:
  Ascends : y = x + a, or Descends : y = x - a.
  Both positions must be in [0, n]. -/
def move (n a b : ℕ) : ℕ → ℕ → Prop := ReflTransGen (fun x y => x ≤ n ∧ y ≤ n ∧ (x + a = y ∨ x = y + b))

/- If one can move from x to y through +a / -b, then he can also move from y to x through +b / -a -/
lemma move_symm (h : move n a b x y) : move n b a y x := by
  induction h with
  | refl => apply ReflTransGen.refl
  | tail tail head ih =>
    obtain ⟨h₁, h₂, h₃⟩ := head
    rename_i y z
    apply ReflTransGen.trans ?_ ih
    apply ReflTransGen.single
    simp [h₁, h₂]
    rcases h₃ with h | h
    all_goals simp [h]

/- If one can move from x to y throught a/b, then it can also move from kx to ky through ka/ kb. -/
lemma move_mul_iff_move (hk : k ≠ 0) : move n a b x y ↔ move (k * n) (k * a) (k * b) (k * x) (k * y) := by
  constructor <;> intro h
  · -- If move n a b x y, prove by induction.
    induction h with
    | refl => apply ReflTransGen.refl
    | tail tail head ih =>
      obtain ⟨h₁, h₂, h₃⟩ := head
      rename_i y z
      apply ReflTransGen.trans ih
      apply ReflTransGen.single
      split_ands
      · exact Nat.mul_le_mul_left k h₁
      · exact Nat.mul_le_mul_left k h₂
      · rcases h₃ with h | h
        · simp [←h]; left; ring
        · simp [h]; right; ring
  · -- If move (k * n) (k * a) (k * b) (k * x) (k * y), we also prove by induction.
    set y' := k * y with hy'
    clear_value y'
    induction h generalizing y with
    | refl =>
      simp [hk] at hy'
      simp [hy']
      apply ReflTransGen.refl
    | tail tail head ih =>
      obtain ⟨h₁, h₂, h₃⟩ := head
      rename_i u z
      rcases h₃ with h | h
      · have hu : u = k * (y - a) := by
          rw [Nat.mul_sub, ←hy']
          exact Nat.eq_sub_of_add_eq h
        apply ReflTransGen.trans (ih hu)
        apply ReflTransGen.single
        split_ands
        · rw [hu] at h₁
          exact le_of_nsmul_le_nsmul_right hk h₁
        · rw [hy'] at h₂
          exact le_of_nsmul_le_nsmul_right hk h₂
        · left; rw [Nat.sub_add_cancel]
          rw [hy'] at h
          apply le_of_nsmul_le_nsmul_right hk
          simp [←h]
      · have hu : u = k * (y + b) := by simp [h, hy']; ring
        apply ReflTransGen.trans (ih hu)
        apply ReflTransGen.single
        split_ands
        · simp [hu] at h₁
          exact le_of_nsmul_le_nsmul_right hk h₁
        · simp [hy'] at h₂
          exact le_of_nsmul_le_nsmul_right hk h₂
        · simp

/- If one can move form x to y through a b such that d ∣ a b and x, then d ∣ y. -/
lemma dvd_tgt_of_dvd_a_b (ha : d ∣ a) (hb : d ∣ b) (hx : d ∣ x) (h : move n a b x y) : d ∣ y := by
  induction h with
  | refl => exact hx
  | tail tail head ih =>
    obtain ⟨h₁, h₂, h₃⟩ := head
    rename_i y z
    rcases h₃ with h | h
    · rw [←h]; exact (Nat.dvd_add_iff_right ih).mp ha
    · rw [h] at ih; exact (Nat.dvd_add_iff_left hb).mpr ih

/- Reduce the general situation to the case of gcd a b = 1. -/
lemma reduce_case_gcd (hne : Nat.gcd a b ≠ 0) (h : IsLeast {n | n > 0 ∧ move n (a / Nat.gcd a b) (b / Nat.gcd a b) 0 n ∧ move n (a / Nat.gcd a b) (b / Nat.gcd a b) n 0} m) :
    IsLeast {n | n > 0 ∧ move n a b 0 n ∧ move n a b n 0} (Nat.gcd a b * m) := by
  constructor
  · -- a.gcd b * m is in the set.
    split_ands
    · simp [h.1.1]
      positivity
    · -- Note that a = a / gcd * gcd a b, b = b / gcd * gcd a b.
      -- Apply move_mul_iff_move, and the results follow.
      obtain h := move_mul_iff_move hne |>.mp h.1.2.1
      simpa [Nat.mul_div_cancel' (Nat.gcd_dvd_right a b), Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)] using h
    · obtain h := move_mul_iff_move hne |>.mp h.1.2.2
      simpa [Nat.mul_div_cancel' (Nat.gcd_dvd_right a b), Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)] using h
  · -- If n is in the set, then we prove that n ≥ a.gcd b * m.
    intro n hn
    simp at hn
    -- Note that we have Nat.gcd a b ∣ n since Nat.gcd a b ∣ a and Nat.gcd a b ∣ b.
    -- Assume that n = Nat.gcd a b * m'.
    have ⟨m, hm⟩ : Nat.gcd a b ∣ n := dvd_tgt_of_dvd_a_b (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b) (by simp) hn.2.1
    -- Therefore, we can show that m' is in {n | n > 0 ∧ move n (a / Nat.gcd a b) (b / Nat.gcd a b) 0 n ∧ move n (a / Nat.gcd a b) (b / Nat.gcd a b) n 0}
    have : m > 0 ∧ move m (a / Nat.gcd a b) (b / Nat.gcd a b) 0 m ∧ move m (a / Nat.gcd a b) (b / Nat.gcd a b) m 0 := by
      split_ands
      · obtain h := hn.1
        simp [hm] at h
        exact h.2
      any_goals
        apply move_mul_iff_move (hne) |>.mpr
        simp [Nat.mul_div_cancel' (Nat.gcd_dvd_right a b), Nat.mul_div_cancel' (Nat.gcd_dvd_left a b), ←hm]
      · exact hn.2.1
      · exact hn.2.2
    -- Therefore, m' ≥ m and n ≥ a.gcd b * m.
    apply h.2 at this
    simp [hm]
    exact Nat.mul_le_mul_left (a.gcd b) this

/- If b ≥ 1 and k ≤ n, and n ≥ a + b - 1, then one can move from k to (k + m * a) % b -/
lemma move_from_k_to_k_add_m_mul_a_mod {n a b k m : ℕ} (hb : b ≥ 1) (hk : k ≤ n) (hn : n ≥ a + b - 1) : move n a b k ((k + m * a) % b) := by
  -- First, we prove by induction that one can move from k to k % b.
  have move_from_k_to_k_mod {n a b k : ℕ} (hk : k ≤ n) : move n a b k (k % b) := by
    set u := k / b
    set v := k % b
    have hm : k = b * u + v := by exact Eq.symm (Nat.div_add_mod k b)
    clear_value u v
    rw [hm] at hk ⊢
    clear hm
    induction u with
    | zero =>
      simp
      apply ReflTransGen.refl
    | succ u ih =>
      -- In fact, since k ≤ n, we have k → k - b → ... → k % b
      have hle : b * u + v ≤ n := by
        apply le_trans ?_ hk
        gcongr
        simp
      apply ReflTransGen.trans ?_ (ih hle)
      · apply ReflTransGen.single
        simp [hk, hle]
        right
        ring
  have hle {k : ℕ} : k % b + a ≤ n := by
    apply le_trans ?_ hn
    rw [add_comm, Nat.add_sub_assoc hb]
    gcongr
    apply Nat.le_pred_of_lt
    apply Nat.mod_lt
    positivity
  -- Then, prove by induction on m
  induction m with
  | zero => simp; exact move_from_k_to_k_mod hk
  | succ m ih =>
    -- we show that k → (k + m * a) % b → (k + m * a) % b + a → (k + (m + 1) * a) % b
    -- The first step is done by ih
    apply ReflTransGen.trans ih
    -- SInce (k + m * a) % b + a ≤ b - 1 + a ≤ n, the second step holds.
    apply ReflTransGen.trans (b := (k + m * a) % b + a)
    · apply ReflTransGen.single
      simp
      constructor
      · apply le_trans ?_ (hle (k := k + m * a)); simp
      · apply hle
    · -- The third step is also done by move_from_k_to_k_mod since ((k + m * a) % b + a) % b = (k + (m + 1) * a) % b.
      apply ReflTransGen.trans (move_from_k_to_k_mod ?_)
      · rw [Nat.add_mod, add_mul, ←add_assoc]; simp
        apply ReflTransGen.refl
      · apply hle

/- We prove that if one can move from x to y, then ∃ m such that
  i) y % b = (x + m * a) % b;
  ii) ∀ i < m, (x + i * a) % b ≤ n; and
  iii) If x < y, then m > 0. -/
lemma exists_m_tgt_eq_m_mul_a_mod {n a b x y : ℕ} (h : move n a b x y) : ∃ m : ℕ, y % b = (x + m * a) % b ∧ (∀ i < m, (x + i * a) % b + a ≤ n) ∧ (x < y → m > 0) := by
  -- prove by induction on the move relation.
  induction h with
  | refl => use 0; simp
  | tail tail head ih =>
    obtain ⟨h₁, h₂, h₃⟩ := head
    rename_i y z
    -- Assume that x → y → z
    obtain ⟨m, hm, hmi, h_pos⟩ := ih
    rcases h₃ with h | h
    · -- Case 1: y + a = z,
      -- use m + 1 and m + 1 > 0 is trivial.
      use m + 1; simp [←h]
      constructor
      · rw [Nat.add_mod, hm]
        simp
        ring_nf
      · intro i hi
        by_cases hi : i < m
        · apply hmi i hi
        · simp at hi
          have : i = m := by
            apply Nat.le_antisymm ?_ hi
            apply Nat.le_of_lt_succ
            assumption
          simp [this, ←hm]
          apply le_trans ?_ h₂
          rw [←h]; gcongr
          exact Nat.mod_le y b
    · -- Case 2: y - b = z
      -- use m
      use m; simp [←hm, h]
      constructor
      · intro i hi
        apply hmi i hi
      · -- If x < z = y - b, then x < y, so m > 0.
        intro hxz
        apply h_pos
        simp [h]
        exact Nat.lt_add_right b hxz

/- If b ≥ 1 and gcd a b = 1, then ∃ m > 1 ∧ b ∣ m * a + n for any n. -/
lemma exists_dvd_of_coprime (hb : b ≥ 1) (hgcd : Nat.gcd a b = 1) (n : ℤ) : ∃ m : ℕ, m > 0 ∧ (b : ℤ) ∣ m * a + n := by
  -- According to the bezout's lemma, ∃ s t such that n = a * s + b * t.
  obtain ⟨s, t, hst⟩ : ∃ (s : ℤ), ∃ (t : ℤ), n = a * s + b * t := by
    obtain ⟨s, t, hst⟩ : ∃ (x : ℤ), ∃ (y : ℤ), n.natAbs = a * x + b * y := by
      apply Int.gcd_dvd_iff.mp
      simp [hgcd]
    by_cases hn : n ≥ 0
    · use s, t
      simp [←hst]
      exact Eq.symm (abs_of_nonneg hn)
    · simp at hn
      use -s, -t
      trans -n.natAbs
      · simp [abs_of_neg hn]
      · simp [hst]; ring
  -- We only need to prove that b ∣ (m + s) * a + b * t for some m > 0, which is equivalent to b ∣ m + s, which is trivial.
  rw [hst]
  let k := ⌈|s| / (b : ℝ)⌉
  set m := (k + 1) * b - s with hm_eq
  have hm : m > 0 := by
    simp [m, k]
    apply lt_of_le_of_lt (b := |s|)
    · exact le_abs_self s
    · apply Int.cast_lt (R := ℝ) |>.mp
      simp
      apply div_lt_iff₀ ?_ |>.mp
      · apply lt_of_le_of_lt (Int.le_ceil _)
        simp
      · norm_cast
  clear_value m
  lift m to ℕ using (le_of_lt hm)
  use m
  have : ↑m * ↑a + (↑a * s + ↑b * t) = ((k + 1) * b) * a + (b * t : ℤ) := by simp [hm_eq]; ring_nf
  norm_cast at hm
  simp [this, hm]
  apply Int.dvd_add
  · use (k + 1) * a; ring
  · simp

/- If gcd a b = 1 and a > 0 and b > 0, the answer is a + b - 1. -/
lemma caes_gcd_eq_one (ha : a > 0) (hb : b > 0) (hgcd : Nat.gcd a b = 1) : IsLeast {n | n > 0 ∧ move n a b 0 n ∧ move n a b n 0} (a + b - 1) := by
  constructor
  · -- We show that there is a sequence of ascending and descending steps that can reach the top rung and come back down when n = a + b - 1.
    split_ands
    · rw [Nat.add_sub_assoc hb]
      positivity
    · -- We have show that one can move from 0 to (m * a) % b for some m.
      apply ReflTransGen.trans (b := b - 1)
      · -- Also ∃ m such that (0 + m * a) % b = b - 1.
        -- Therefore, 0 → b - 1 holds
        obtain ⟨m, hm⟩ : ∃ m, (0 + m * a) % b = b - 1 := by
          obtain ⟨m, hm, hdvd⟩ := exists_dvd_of_coprime hb hgcd 1
          use m
          apply Nat.cast_inj (R := ℤ) |>.mp
          rw [Nat.cast_sub hb]
          simp
          trans (b - 1) % b
          · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
            simp
            have : ↑m * ↑a - (↑b - 1) = m * a + 1 - (b : ℤ) := by ring
            simp [this, hdvd]
          · apply Int.emod_eq_of_lt
            · simp; exact hb
            · simp
        rw [←hm]
        apply move_from_k_to_k_add_m_mul_a_mod hb (by simp) (by simp)
      · -- b - 1 → a + b - 1 is trivial.
        apply ReflTransGen.single
        simp
        constructor
        · rw [Nat.sub_add_cancel]
          · simp
          · exact Nat.le_add_right_of_le ha
        · left
          rw [←Nat.sub_add_comm hb, add_comm]
    · -- We proved that n → (n + m * a) % b for some m.
      -- Since ∃ m, (n + m * a) % b = 0, we can move from n to 0.
      obtain ⟨m, hm⟩ : ∃ m, ((a + b - 1) + m * a) % b = 0 := by
        obtain ⟨m, hm, hdvd⟩ := exists_dvd_of_coprime hb hgcd (-1)
        use (m - 1)
        apply Nat.cast_inj (R := ℤ) |>.mp
        simp [Nat.cast_sub hm]
        rw [Nat.cast_sub (by exact Nat.le_add_right_of_le ha)]
        simp
        have : ↑a + ↑b - 1 + (m - 1) * ↑a = m * a + (-1 : ℤ) + b := by ring
        simp [this]
        exact hdvd
      rw [←hm]
      exact move_from_k_to_k_add_m_mul_a_mod hb (by simp) (by simp)
  · -- Assume that n is in the set, we show that n ≥ a + b - 1.
    intro n hn
    obtain ⟨hn_pos, hasc, hdsc⟩ := hn
    -- Since one can move from 0 to n, there exists m such that n % b = (m * a) % b ∧ (∀ i < m, (i * a) % b + a ≤ n) ∧ m > 0 (since 0 < n).
    obtain ⟨m₁, hm₁, hmi₁, h_pos⟩ := exists_m_tgt_eq_m_mul_a_mod hasc
    -- Similarly, there exists m such that 0 = (n + m * a) % b ∧ (∀ i < m, (n + i * a) % b + a ≤ n).
    obtain ⟨m₂, hm₂, hmi₂, _⟩ := exists_m_tgt_eq_m_mul_a_mod hdsc
    have hm₁_pos : m₁ > 0 := by apply h_pos hn_pos
    simp at hm₁ hm₂
    -- let m = m₁ + m₂, we show that (m * a) % b = 0 and ∀ i < m, (i * a) % b + a ≤ n.
    let m := m₁ + m₂
    have hm : (m * a) % b = 0 := by
      rw [add_mul, Nat.add_mod, ←hm₁, hm₂]
      simp
    have hmi : ∀ i < m, (i * a) % b + a ≤ n := by
      intro i hi
      by_cases hi₁ : i < m₁
      · obtain h := hmi₁ i hi₁
        simp at h
        apply h
      · simp at hi₁
        let i₂ := i - m₁
        have hi : i = m₁ + i₂ := by exact Eq.symm (Nat.add_sub_of_le hi₁)
        have hi₂ : i₂ < m₂ := by exact Nat.sub_lt_left_of_lt_add hi₁ (by assumption)
        apply hmi₂ at hi₂
        apply le_of_eq_of_le ?_ hi₂
        congr 1
        rw [hi, add_mul, Nat.add_mod, ←hm₁]
        simp
    -- But we can also find some i ≤ m such that i > 0 ∧ (i * a) % b = b - 1.
    obtain ⟨i, hi, hi_pos, hmod⟩ : ∃ i ≤ m, i > 0 ∧ (i * a) % b = b - 1 := by
      -- We prove that there exists i such that b ∣ i * a + (1 - b).
      -- Choose the smallest i such that b ∣ i * a + (1 - b).
      let i := Nat.find (exists_dvd_of_coprime hb hgcd (1 - b))
      have hi : i > 0 ∧ (b : ℤ) ∣ ↑i * ↑a + (1 - b) := by apply Nat.find_spec (exists_dvd_of_coprime hb hgcd (1 - b))
      use i
      split_ands
      · -- We show that i ≤ m, otherwise, we can find i - m also satisfies the condition.
        -- So i - m ≤ m, which implies m = 0.
        by_contra h
        simp at h
        let j := i - m
        have hj : j > 0 ∧ (b : ℤ) ∣ ↑j * ↑a + (1 - b) := by
          simp [j, h]
          have : ↑(i - m) * ↑a + (1 - ↑b) = i * a + (1 - b) - (m * a : ℤ) := by rw [Nat.cast_sub (le_of_lt h)]; ring
          rw [this]
          apply Int.dvd_sub hi.2
          norm_cast
          exact Nat.dvd_of_mod_eq_zero hm
        have hij : i ≤ j := by apply Nat.find_le hj
        simp [j] at hij
        apply Nat.add_le_of_le_sub (le_of_lt h) at hij
        simp [m] at hij
        -- However, m ≥ m₁ > 0, which is a contradiction.
        simp [hij] at hm₁_pos
      · exact hi.1
      · -- i * a % b = b - 1.
        apply Nat.cast_inj (R := ℤ) |>.mp
        simp [Nat.cast_sub hb]
        trans (b - 1) % b
        · apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
          simp
          have : ↑i * ↑a - (↑b - 1) = i * a + (1 - (b : ℤ)) := by ring
          simp [this, hi.2]
        · apply Int.emod_eq_of_lt
          · simp; exact hb
          · simp
    rcases lt_or_eq_of_le hi with h | h
    · -- If i < m, then we have b - 1 + a = (i * a) % b + 1 ≤ n.
      -- Therefore, n ≥ a + b - 1.
      apply hmi at h
      rw [hmod] at h
      apply le_of_eq_of_le ?_ h
      rw [←Nat.sub_add_comm hb, add_comm]
    · -- If i = m, then we have b - 1 = (m * a) % b = 0, which implies b = 1.
      simp [h] at hmod
      simp [hmod] at hm
      have hb : b = 1 := by
        apply le_antisymm ?_ hb
        exact Nat.le_of_sub_eq_zero hm
      simp [hb]
      -- We only need to show that n ≥ a.
      -- However, since 0 < i, we have (0 + i * a) % b + a ≤ n.
      -- Hence, n ≥ a.
      obtain h := hmi₁ 0 hm₁_pos
      simpa using h

/-13. (IRE 2) An eccentric mathematician has a ladder with $n$ rungs that he always ascends and descends
  in the following way: When he ascends, each step he takes covers $a$ rungs of the ladder, and when he descends,
  each step he takes covers $b$ rungs of the ladder, where $a$ and $b$ are fixed positive integers.
  By a sequence of ascending and descending steps he can climb from ground level to the top rung of the ladder
  and come back down to ground level again. Find, with proof, the minimum value of $n$, expressed in terms of $a$ and $b$.-/
theorem number_theory_24276 (a b : ℕ)(ha : a > 0) (hb : b > 0) :
    IsLeast {n : ℕ | n > 0 ∧ move n a b 0 n ∧ move n a b n 0} (a + b - Nat.gcd a b) := by
  -- wlog, we assume that gcd a b = 1.
  wlog hgcd : Nat.gcd a b = 1 with H
  · -- Otherwise, let a' = a / Nat.gcd a b and b' = b / Nat.gcd a b.
    let a' := a / Nat.gcd a b
    let b' := b / Nat.gcd a b
    -- Now we have gcd a' b' = 1.

    have hne : Nat.gcd a b ≠ 0 := by exact Nat.gcd_ne_zero_left (by positivity)
    have ha' : a' > 0 := by
      simp [a']
      constructor
      · positivity
      · exact Nat.gcd_le_left b ha
    have hb' : b' > 0 := by
      simp [b']
      constructor
      · positivity
      · exact Nat.gcd_le_right b hb
    have hgcd : Nat.gcd a' b' = 1 := by
      rw [Nat.gcd_div]
      · apply Nat.div_self; exact Nat.gcd_pos_of_pos_left b ha
      · exact Nat.gcd_dvd_left a b
      · exact Nat.gcd_dvd_right a b
    -- Applying Lemma reduce_case_gcd, we can reduce the case to gcd a' b' = 1.
    obtain h := reduce_case_gcd hne (H a' b' ha' hb' hgcd)
    simpa [Nat.mul_sub, mul_add, Nat.mul_div_cancel' (Nat.gcd_dvd_right a b), Nat.mul_div_cancel' (Nat.gcd_dvd_left a b), hgcd] using h
  · -- If gcd a b = 1, we can use caes_gcd_eq_one to prove the result.
    simp [hgcd]
    exact caes_gcd_eq_one ha hb hgcd
