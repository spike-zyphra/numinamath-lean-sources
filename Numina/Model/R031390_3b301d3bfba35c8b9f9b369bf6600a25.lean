import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_263198 {f : ℝ → ℝ} (hf : ∀ x ∈ (Icc (-2) 2), f x = f (-x)) (hfd : AntitoneOn f (Icc 0 2)) (hm : 1-m ∈ (Icc (-2) 2) ∧ m ∈ (Icc (-2) 2)) : (f (1 - m) < f m) → (-1 ≤ m ∧ m < 1 / 2) := by
  intro h
  rcases hm with ⟨h1m, hm⟩
  have h1m1 : -2 ≤ 1 - m ∧ 1 - m ≤ 2 := by
    have h1m' : 1 - m ∈ Set.Icc (-2) 2 := h1m
    exact h1m'
  have hm1 : -2 ≤ m ∧ m ≤ 2 := by
    have hm' : m ∈ Set.Icc (-2) 2 := hm
    exact hm'
  have h2 : -1 ≤ m := by
    nlinarith [h1m1.right, hm1.left]
  have h4 : m < 1 / 2 := by
    by_contra h4'
    push_neg at h4'
    have h4' : m ≥ 1 / 2 := by nlinarith
    by_cases h5 : m ≤ 1
    · -- case where $0 \leq m \leq 1$
      have h7 : 1 - m ≥ 0 := by nlinarith
      have h7 : (1 - m : ℝ) ∈ Set.Icc (0 : ℝ) 2 := by
        constructor
        · nlinarith
        · nlinarith
      have h8 : (m : ℝ) ∈ Set.Icc (0 : ℝ) 2 := by
        constructor
        · nlinarith
        · nlinarith
      have h16 : f (1 - m) ≥ f m := by
        apply hfd
        all_goals
        all_goals
        all_goals
        all_goals
        all_goals
        all_goals
        try { tauto }
        all_goals
        try { nlinarith }
        all_goals
        try { nlinarith }
        all_goals
        try { all_goals nlinarith }
      linarith
      all_goals tauto
      all_goals nlinarith
    · -- case where $1 < m \leq 2$
      push_neg at h5
      have h8 : m - 1 ≥ 0 := by nlinarith
      have h16 : (1 - m : ℝ) ≤ (0 : ℝ) := by nlinarith
      have h9 : f (1 - m) = f (m - 1 : ℝ) := by
        have h91 : (1 - m : ℝ) ∈ Set.Icc (-2) 2 := by
          constructor
          · nlinarith
          · nlinarith
        have h92 : (m - 1 : ℝ) ∈ Set.Icc (-2) 2 := by
          constructor
          · nlinarith
          · nlinarith
        calc
          f (1 - m : ℝ) = f (-(m - 1 : ℝ)) := by 
            ring_nf
            <;> try { norm_num [show (1 - (m : ℝ) = -(m - 1 : ℝ) ) by nlinarith] }
          _ = f (m - 1 : ℝ) := by
            rw [hf (m - 1: ℝ) (by
              constructor
              · nlinarith
              · nlinarith
            )]
            <;> ring_nf <;> try { norm_num }
      have h17 : (m - 1 : ℝ) ∈ Set.Icc (0 : ℝ) 2 := by
        constructor <;> nlinarith
      have h18 : (m : ℝ) ∈ Set.Icc (0 : ℝ) 2 := by
        constructor <;> nlinarith
      have h19 : f (m - 1 : ℝ) ≥ f m := by
        apply hfd
        all_goals
        all_goals
        all_goals
        all_goals
        all_goals
        try { tauto }
        all_goals
        try { nlinarith }
        all_goals
        try { nlinarith }
        all_goals
        try { all_goals nlinarith }
      have h20 : f (1 - m) ≥ f m := by
        linarith [h9, h19]
      linarith
  exact ⟨h2, h4⟩
  all_goals nlinarith
  all_goals try { linarith }
  all_goals
  try { tauto }
  all_goals
  try { nlinarith }
  all_goals
  try { nlinarith }
  all_goals
  try { tauto }
  all_goals
  try { nlinarith }
  all_goals
  try { tauto }
  all_goals
  try { nlinarith }
  all_goals
  try { tauto }
  all_goals
  try { nlinarith }
  all_goals
  try { tauto }
  all_goals
  try { nlinarith }
  all_goals
  try { tauto }
  all_goals
  try { nlinarith }