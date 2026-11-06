import Mathlib

theorem number_theory_265001 (a b : ℕ) (ha : a = 1580) (h : ∃ x y z w v u : ℕ,
    x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ x ≠ v ∧ x ≠ u ∧ y ≠ z ∧ y ≠ w ∧ y ≠ v ∧ y ≠ u ∧
    z ≠ w ∧ z ≠ v ∧ z ≠ u ∧ w ≠ v ∧ w ≠ u ∧ v ≠ u ∧ (x + y) / 2 = a ∧
    (x + z) / 2 = b ∧ (x + w) / 2 = a ∧ (x + v) / 2 = b ∧ (x + u) / 2 = a ∧
    (y + z) / 2 = b ∧ (y + w) / 2 = a ∧ (y + v) / 2 = b ∧ (y + u) / 2 = a ∧
    (z + w) / 2 = b ∧ (z + v) / 2 = a ∧ (z + u) / 2 = b ∧ (w + v) / 2 = a ∧
    (w + u) / 2 = b ∧ (v + u) / 2 = a) :
    a = 1580 ∧ b = 556 := by
  constructor
  · exact ha
  · 
    rcases h with ⟨x, y, z, w, v, u, hxy, hxz, hxw, hxv, hxu, hyz, hyw, hyv, hyu, hzw, hzv, hzu, hwv, hwu, hvu, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
    omega
    <;> try { tauto }
    <;> try { omega }
    <;> try { tauto }
    <;> try { omega }
    <;> try { tauto }
    <;> try { omega }
    <;> try { tauto }
    <;> try { omega }
    <;> try { tauto }
    all_goals omega
    <;> try { tauto }
    <;> try { omega }
    <;> try { tauto }
    all_goals tauto