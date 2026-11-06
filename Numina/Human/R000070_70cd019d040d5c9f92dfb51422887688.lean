import Mathlib

open Classical

-- 定义两位数的十位数字
@[simp]
def ten (n : Nat) := n / 10
-- 定义两位数的个位数字
@[simp]
def unit (n : Nat) := n % 10

/--a b 相差12时，它们的个位数字和十位数字均不相等 -/ 
lemma unit_ne_diff12 {a b : ℕ} (h : a = b + 12) : unit a ≠ unit b := by
  simp [unit, h, Nat.add_mod]
  norm_num
  rw [←Nat.ModEq, Nat.modEq_iff_dvd]
  simp only [Nat.cast_add, sub_add_cancel_left, Int.reduceNeg]
  norm_num

lemma ten_ne_diff12 (h : a = b + 12) : ten a ≠ ten b := by
  simp [ten, h, Nat.add_div]
  by_cases h1 : 8 ≤ b % 10 <;> simp [h1]; linarith

-- 由以上，若 a b十进制表示中存在相等的数字，只能是a的十位数字等于b的个位数字或
-- a的个位数字等于b的十位数字
lemma cond_cases (h1 : a = b + 12)
    (h2 : ten a = ten b ∨ ten a = unit b ∨ unit a = ten b ∨ unit a = unit b) : 
    ten a = unit b ∨ unit a = ten b := by
  have := unit_ne_diff12 h1
  have := ten_ne_diff12 h1
  tauto
      

-- 在题设条件下 b的个位数字必须小于 8
lemma unitb_lt8 (hh : (10 ≤ a ∧ a < 100) ∧ ((10 ≤ b ∧ b < 100))) (h1 : a = b + 12) 
    (h2 : ten a = unit b ∨ unit a = ten b)
    (h3 : ten a + unit a = ten b + unit b + 3) : unit b < 8 := by
  by_contra! h; simp at h
  set c := b % 10 with hc
  have : c < 10 := Nat.mod_lt b (by simp)
  interval_cases c <;> simp [ten, unit, ←hc] at h2
  · have h4 : unit a = 0 := by simp [unit, h1, Nat.add_mod, ←hc];
    rcases h2 with hl | hr
    · have ha : a = 80 := by simp [unit] at h4; rw [←Nat.div_add_mod a 10, hl, h4]
      have hb : b = 68 := by linarith
      simp [ha, hb, ten, unit] at h3
    · simp at h4; simp [h4] at hr; symm at hr; simp [ Nat.div_eq_zero_iff ] at hr
      linarith
  · have h4 : unit a = 1 := by simp [unit, h1, Nat.add_mod, ←hc]
    rcases h2 with hl | hr
    · have ha : a = 91 := by simp [unit] at h4; rw [←Nat.div_add_mod a 10, hl, h4]
      have hb : b = 79 := by linarith
      simp [ha, hb, ten, unit] at h3
    · simp at h4; simp [h4] at hr; symm at hr
      have hb : b = 19 := by rw [←Nat.div_add_mod b 10, hr, ←hc]
      have ha : a = 31 := by linarith
      simp [ha, hb] at h3

lemma unita_eq_unitb_add_two (hh : (10 ≤ a ∧ a < 100) ∧ ((10 ≤ b ∧ b < 100))) 
    (h1 : a = b + 12) (h2 : ten a = unit b ∨ unit a = ten b)
    (h3 : ten a + unit a = ten b + unit b + 3) : unit a = unit b + 2 := by
  simp [unit, h1, Nat.add_mod]
  rw [Nat.mod_mod b 10, show 2 % 10 = 2 by simp, ];
  by_cases h : b % 10 + 2 < 10
  · exact (Nat.mod_eq_iff_lt (by simp)).2 h
  · simp at h; have := unitb_lt8 hh h1 h2 h3; simp at this
    linarith

lemma tena_eq_tenb_add_one (hh : (10 ≤ a ∧ a < 100) ∧ ((10 ≤ b ∧ b < 100))) (h1 : a = b + 12) 
    (h2 : ten a = unit b ∨ unit a = ten b) (h3 : ten a + unit a = ten b + unit b + 3) : 
    ten a = ten b + 1 := by
  rw [unita_eq_unitb_add_two hh h1 h2 h3] at h3
  linarith

-- a的十位数字等于 b 个位数字情形
theorem id4214_case1b (hh : (10 ≤ a ∧ a < 100) ∧ ((10 ≤ b ∧ b < 100))) (h1 : a = b + 12)
    (h2 : ten a = unit b) (h3 : ten a + unit a = ten b + unit b + 3) :
    b = 12 ∨ b = 23 ∨ b = 34 ∨ b = 45 ∨ b = 56 ∨ b = 67 := by
  have h1' := tena_eq_tenb_add_one hh h1 (Or.inl h2) h3
  have h2' := unita_eq_unitb_add_two hh h1 (Or.inl h2) h3
  have : ten b < 7 := by have := h2 ▸ (unitb_lt8 hh h1 (Or.inl h2) h3); linarith
  have : 1 ≤ ten b := by simp; exact (Nat.one_le_div_iff (by simp)).mpr hh.2.1
  rw [h1'] at h2; rw [←h2] at h2'
  set c := ten b with hc
  interval_cases c <;> simp at h2 hc <;> rw [←Nat.div_add_mod b 10, ←h2, ←hc] <;> tauto

theorem id4214_case1a (hh : (10 ≤ a ∧ a < 100) ∧ ((10 ≤ b ∧ b < 100))) (h1 : a = b + 12)
    (h2 : ten a = unit b) (h3 : ten a + unit a = ten b + unit b + 3) :
    a = 24 ∨ a = 35 ∨ a = 46 ∨ a = 57 ∨ a = 68 ∨ a = 79 := by
  have := id4214_case1b hh h1 h2 h3
  simpa [h1]

-- a的个位数字等于 b十位数字情形
theorem id4214_case2b (hh : (10 ≤ a ∧ a < 100) ∧ ((10 ≤ b ∧ b < 100))) (h1 : a = b + 12)
    (h2 : unit a = ten b) (h3 : ten a + unit a = ten b + unit b + 3) :
    b = 20 ∨ b = 31 ∨ b = 42 ∨ b = 53 ∨ b = 64 ∨ b = 75 ∨ b = 86 := by
  have h1' := tena_eq_tenb_add_one hh h1 (Or.inr h2) h3
  have h2' := unita_eq_unitb_add_two hh h1 (Or.inr h2) h3
  rw [h2'] at h2
  have : 2 ≤ ten b := by
    have : 0 ≤ unit b := by simp
    linarith
  have : ten b < 9 := by
    by_contra! h4;
    have : 90 ≤ b := by simp at h4; exact Nat.mul_le_of_le_div 10 9 b h4
    have : 102 ≤ a := by linarith
    linarith
  set c := ten b with hc
  interval_cases c <;> simp at h2 hc <;> rw [←Nat.div_add_mod b 10, h2, ←hc] <;> tauto

theorem id4214_case2a (hh : (10 ≤ a ∧ a < 100) ∧ ((10 ≤ b ∧ b < 100))) (h1 : a = b + 12)
    (h2 : unit a = ten b) (h3 : ten a + unit a = ten b + unit b + 3) :
    a = 32 ∨ a = 43 ∨ a = 54 ∨ a = 65 ∨ a = 76 ∨ a = 87 ∨ a = 98 := by
  have := id4214_case2b hh h1 h2 h3
  simpa [h1]
