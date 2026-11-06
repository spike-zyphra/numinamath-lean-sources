import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_275498 {a : ℝ} (ha : a ≠ 0) :
  /- 定义三次抛物线函数 y = ax³ -/
  let cubic := fun x : ℝ => a * x^3
  
  /- 定义线段 AB 的中点函数：
     A 是曲线上坐标为 (p, ap³) 的点
     B 是切线与 Y 轴的交点，坐标为 (0, -2ap³) -/
  let midpoint_AB := fun p : ℝ =>
    let A := (p, cubic p)                           -- 点 A 的坐标
    let tangent_slope := 3 * a * p^2                -- 切线斜率
    let tangent := fun x => tangent_slope * (x - p) + cubic p  -- 切线方程
    let B := (0, tangent 0)                         -- 点 B 的坐标
    ((A.1 + B.1) / 2, (A.2 + B.2) / 2)              -- AB 的中点坐标
  
  /- 定义线段 BC 的中点函数：
     B 同上
     C 是切线与曲线的另一个交点，坐标为 (-2p, -8ap³) -/
  let midpoint_BC := fun p : ℝ =>
    let A := (p, cubic p)
    let tangent_slope := 3 * a * p^2
    let tangent := fun x => tangent_slope * (x - p) + cubic p
    let B := (0, tangent 0)
    let C := (-2 * p, cubic (-2 * p))               -- 点 C 的坐标
    ((B.1 + C.1) / 2, (B.2 + C.2) / 2)              -- BC 的中点坐标
  
  /- 定义 AB 中点的轨迹集合 -/
  let locus_AB := {m | ∃ p : ℝ, m = midpoint_AB p}
  
  /- 定义 BC 中点的轨迹集合 -/
  let locus_BC := {m | ∃ p : ℝ, m = midpoint_BC p}
  
  /- 证明 AB 中点的轨迹是 y = -4ax³，BC 中点的轨迹是 y = 5ax³ -/
  (∀ x y : ℝ, (x, y) ∈ locus_AB ↔ y = -4 * a * x^3) ∧
  (∀ x y : ℝ, (x, y) ∈ locus_BC ↔ y = 5 * a * x^3) := by
  constructor
  · -- Show that the midpoint of AB is y = -4ax³
    intro x y
    constructor
    · -- Forward direction: existence of midpoint implies equation
      rintro ⟨p, hp⟩
      simp [Prod.ext_iff] at hp
      have h_eq1 : x = p / 2 := by 
        linarith
      -- Compute y
      have h_eq2 : y = (a * p^3 + (-2 * a * p^3)) / 2 := by
        -- First tangent slope
        have tangent_slope : 3 * a * p^2 = 3 * a * p^2 := by rfl
        -- Let tangent be the tangent line function
        have tangent_0 : (3 * a * p^2) * (0 - p) + a * p^3 = -2 * a * p^3 := by
          calc
            (3 * a * p^2) * (0 - p) + a * p^3 
              = (3 * a * p^2) * (-p) + a * p^3 := by ring
            _ = -3 * a * p^3 + a * p^3 := by ring
            _ = -2 * a * p^3 := by ring
        nlinarith [hp.2, tangent_0]
      have hp_eq1 : p = 2 * x := by linarith
      rw [hp_eq1] at h_eq2
      ring_nf at h_eq2
      linarith
    · -- Backward direction: equation implies existence of midpoint
      intro h_eq
      use 2 * x
      simp [Prod.ext_iff] at *
      all_goals 
        ring_nf at h_eq ⊢
        <;> linarith [h_eq]
  · -- Show that the midpoint of BC is y = 5ax³
    intro x y
    constructor
    · -- Forward direction: existence of midpoint implies equation
      rintro ⟨p, hp⟩
      simp [Prod.ext_iff] at hp
      have h_eq1 : x = -p := by
        linarith
      -- Compute y
      have h_eq2 : y = ( -2 * a * p^3 + a * (-2 * p) ^3 ) / 2 := by 
        -- First tangent slope
        have tangent_slope : 3 * a * p^2 = 3 * a * p^2 := by rfl
        -- Let tangent be the tangent line function
        have tangent_0 : (3 * a * p^2) * (0 - p) + a * p^3 = -2 * a * p^3 := by 
          calc
            (3 * a * p^2) * (0 - p) + a * p^3 
              = (3 * a * p^2) * (-p) + a * p^3 := by ring
            _ = -3 * a * p^3 + a * p^3 := by ring
            _ = -2 * a * p^3 := by ring
        nlinarith [hp.2, tangent_0]
      have hp_eq1 : p = -x := by linarith 
      rw [hp_eq1] at h_eq2 
      ring_nf at h_eq2 
      linarith
    · -- Backward direction: equation implies existence of midpoint
      intro h_eq 
      use -x 
      simp [Prod.ext_iff] at *
      all_goals 
        ring_nf at h_eq ⊢
        <;> linarith [h_eq]