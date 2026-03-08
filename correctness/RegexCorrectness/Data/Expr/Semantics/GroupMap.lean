module

public import RegexCorrectness.Data.Expr.Semantics.CaptureGroups
public import Mathlib.Data.DFinsupp.Defs

open String (Pos)

@[expose]
public section

namespace Regex.Data.Expr

variable {s : String}

inductive GroupInfo (s : String) where
  | none
  | started (startAt : Pos s)
  | closed (startAt : Pos s) (endAt : Pos s)
deriving Inhabited

instance : Zero (GroupInfo s) := ⟨.none⟩

structure GroupMap (s : String) where
  groups : DFinsupp (fun (_ : Nat) => GroupInfo s)

namespace GroupMap

def empty {s : String} : GroupMap s := { groups := 0 }

def get (tag : Nat) (self : GroupMap s) : GroupInfo s :=
  self.groups tag

def openGroup (tag : Nat) (startAt : Pos s) (self : GroupMap s) : GroupMap s :=
  { groups := self.groups.update tag (.started startAt) }

def closeGroup (tag : Nat) (endAt : Pos s) (self : GroupMap s) : GroupMap s :=
  match self.get tag with
  | .started startAt => { groups := self.groups.update tag (.closed startAt endAt) }
  | _ => self

def setClosed (tag : Nat) (startAt endAt : Pos s) (self : GroupMap s) : GroupMap s :=
  { groups := self.groups.update tag (.closed startAt endAt) }

def addCaptures (self : GroupMap s) : CaptureGroups s → GroupMap s
  | .empty => self
  | .group tag first last rest => (self.addCaptures rest).setClosed tag first last
  | .concat g₁ g₂ => (self.addCaptures g₁).addCaptures g₂

@[simp] theorem get_openGroup_self (self : GroupMap s) (tag : Nat) (startAt : Pos s) :
  (self.openGroup tag startAt).get tag = .started startAt := by
  simp [openGroup, get]

@[simp] theorem get_openGroup_of_ne (self : GroupMap s) {tag tag' : Nat} (startAt : Pos s) (h : tag' ≠ tag) :
  (self.openGroup tag startAt).get tag' = self.get tag' := by
  simp [openGroup, get, h]

@[simp] theorem get_setClosed_self (self : GroupMap s) (tag : Nat) (startAt endAt : Pos s) :
  (self.setClosed tag startAt endAt).get tag = .closed startAt endAt := by
  simp [setClosed, get]

@[simp] theorem get_setClosed_of_ne (self : GroupMap s) {tag tag' : Nat} (startAt endAt : Pos s) (h : tag' ≠ tag) :
  (self.setClosed tag startAt endAt).get tag' = self.get tag' := by
  simp [setClosed, get, h]

@[simp] theorem get_closeGroup_of_ne (self : GroupMap s) {tag tag' : Nat} (endAt : Pos s) (h : tag' ≠ tag) :
  (self.closeGroup tag endAt).get tag' = self.get tag' := by
  cases hget : self.groups tag <;> simp [closeGroup, get, hget, h]

@[simp] theorem get_closeGroup_self (self : GroupMap s) (tag : Nat) (endAt : Pos s) :
  (self.closeGroup tag endAt).get tag =
    match self.get tag with
    | .started startAt => .closed startAt endAt
    | x => x := by
  cases hget : self.groups tag <;> simp [closeGroup, get, hget]

theorem ext {x y : GroupMap s} (h : ∀ tag, x.get tag = y.get tag) : x = y := by
  cases x with
  | mk xgroups =>
    cases y with
    | mk ygroups =>
      have h' : xgroups = ygroups := DFinsupp.ext h
      simp [h']

theorem openGroup_setClosed_comm (self : GroupMap s) {tag tag' : Nat} {openAt first last : Pos s}
  (h : tag' ≠ tag) :
  (self.openGroup tag openAt).setClosed tag' first last = (self.setClosed tag' first last).openGroup tag openAt := by
  apply ext
  intro i
  by_cases hi : i = tag
  · subst hi
    have h' : i ≠ tag' := by
      exact fun heq => h heq.symm
    simp [GroupMap.get, GroupMap.setClosed, GroupMap.openGroup, Function.update, h']
  · by_cases hi' : i = tag'
    · subst hi'
      simp [get_openGroup_of_ne, h]
    · simp [get_openGroup_of_ne, get_setClosed_of_ne, hi, hi']

theorem get_addCaptures_eq_self_of_forall_not_mem (self : GroupMap s) {groups : CaptureGroups s} {tag : Nat}
  (h : ∀ first last, (tag, first, last) ∉ groups) :
  (self.addCaptures groups).get tag = self.get tag := by
  induction groups generalizing self with
  | empty =>
    simp [addCaptures]
  | group tag' first last rest ih =>
    have hne : tag' ≠ tag := by
      intro heq
      exact h first last (by simp [heq])
    have hne' : tag ≠ tag' := by
      exact fun heq => hne heq.symm
    simpa [addCaptures, GroupMap.get, GroupMap.setClosed, Function.update, hne'] using
      ih self (by
      intro first' last' mem
      exact h first' last' (by simp [mem]))
  | concat g₁ g₂ ih₁ ih₂ =>
    simp [addCaptures]
    rw [ih₂ (self := self.addCaptures g₁) (by
        intro first last mem
        exact h first last (by simp [mem]))]
    exact ih₁ self (by
      intro first last mem
      exact h first last (by simp [mem]))

theorem addCaptures_openGroup_comm_of_forall_not_mem
  (self : GroupMap s) {groups : CaptureGroups s} {tag : Nat} {startAt : Pos s}
  (hmem : ∀ first last, (tag, first, last) ∉ groups) :
  (self.openGroup tag startAt).addCaptures groups = (self.addCaptures groups).openGroup tag startAt := by
  induction groups generalizing self with
  | empty =>
    simp [addCaptures]
  | group tag' first last rest ih =>
    have hne : tag' ≠ tag := by
      intro heq
      exact hmem first last (by simp [heq])
    calc (self.openGroup tag startAt).addCaptures (.group tag' first last rest)
      _ = (((self.openGroup tag startAt).addCaptures rest).setClosed tag' first last) := by
        simp [addCaptures]
      _ = (((self.addCaptures rest).openGroup tag startAt).setClosed tag' first last) := by
        rw [ih self (by
          intro first' last' mem
          exact hmem first' last' (by simp [mem]))]
      _ = (((self.addCaptures rest).setClosed tag' first last).openGroup tag startAt) := by
        rw [openGroup_setClosed_comm _ hne]
      _ = (self.addCaptures (.group tag' first last rest)).openGroup tag startAt := by
        simp [addCaptures]
  | concat g₁ g₂ ih₁ ih₂ =>
    calc (self.openGroup tag startAt).addCaptures (.concat g₁ g₂)
      _ = (((self.openGroup tag startAt).addCaptures g₁).addCaptures g₂) := by
        simp [addCaptures]
      _ = ((((self.addCaptures g₁).openGroup tag startAt)).addCaptures g₂) := by
        rw [ih₁ self (by
          intro first last mem
          exact hmem first last (by simp [mem]))]
      _ = ((((self.addCaptures g₁).addCaptures g₂).openGroup tag startAt)) := by
        rw [ih₂ (self := self.addCaptures g₁) (by
          intro first last mem
          exact hmem first last (by simp [mem]))]
      _ = (self.addCaptures (.concat g₁ g₂)).openGroup tag startAt := by
        simp [addCaptures]

theorem get_addCaptures_openGroup_eq_of_ne
  (self : GroupMap s) {groups : CaptureGroups s} {tag tag' : Nat} {startAt : Pos s}
  (hmem : ∀ first last, (tag, first, last) ∉ groups) (hne : tag' ≠ tag) :
  ((self.openGroup tag startAt).addCaptures groups).get tag' = (self.addCaptures groups).get tag' := by
  rw [addCaptures_openGroup_comm_of_forall_not_mem self hmem]
  simp [get_openGroup_of_ne, hne]

theorem closeGroup_addCaptures_openGroup_eq_addCaptures_group
  (self : GroupMap s) {groups : CaptureGroups s} {tag : Nat} {startAt endAt : Pos s}
  (hmem : ∀ first last, (tag, first, last) ∉ groups) :
  ((self.openGroup tag startAt).addCaptures groups).closeGroup tag endAt =
    self.addCaptures (.group tag startAt endAt groups) := by
  apply ext
  intro tag'
  by_cases h : tag' = tag
  · rw [h, get_closeGroup_self]
    have hstarted :
        ((self.openGroup tag startAt).addCaptures groups).get tag = .started startAt := by
      rw [get_addCaptures_eq_self_of_forall_not_mem (self := self.openGroup tag startAt) (tag := tag) hmem]
      simp
    rw [hstarted]
    simp [addCaptures]
  · rw [get_closeGroup_of_ne _ _ h, get_addCaptures_openGroup_eq_of_ne _ hmem h]
    simp [addCaptures, get_setClosed_of_ne, h]

end GroupMap

end Regex.Data.Expr

end
