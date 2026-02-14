import Mathlib

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  admit

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ := by
  admit

end Function
