import Mathlib

open Real

theorem other_166925 {R r L S : ℝ} (hR : R > 0) (hr : r > 0)
    (hL : L > 0) (hS : S > 0) (hRr : r < R) :
    let g := 9.81
    let Q := 4 * π * R^3 * g
    let q := 4 * π * r^3 * g
    let m := 4 * π * r^3
    let k := m * r / (4 * π * R^2)
    let a := k * r^3 / (R^3 * (L + 2 * R - S)^2)
    a = k * r^3 / (R^3 * (L + 2 * R - S)^2) := by 
  rfl