import ProofWidgets.Component.PenroseDiagram
import ProofWidgets.Component.HtmlDisplay
import Regex.Regex
import Regex.Data.Anchor
import Regex.Data.Classes
import Regex.Syntax.Parser

open Lean Meta ProofWidgets Jsx Regex.Syntax.Parser
open scoped Jsx in

def epsilon : String := "\\epsilon"

def isNeighbor (i j : Nat) : String :=
  if i - j == 1 then "TRUE" else "FALSE"

def escapeLabel (label : String) : String :=
  label.replace "_" "\\_"

def labelElement (elemLabel label : String) : String :=
  if label = "$" then
    s!"Label {elemLabel} \"{label}\"\n"
  else if label = "^" then
    s!"Label {elemLabel} ${label}\\wedge$\n"
  else if label = epsilon then
    s!"Label {elemLabel} ${label}$\n"
  else
    s!"Label {elemLabel} $\\text\{{escapeLabel label}}$\n"

def createNode (i : Nat) : String :=
  s!"Let n{i} := Node(\"{i}\")\n"

def labelNode (i : Nat) (label : String) : String :=
  labelElement s!"n{i}" label

def declareStartNode (i : Nat) : String :=
  s!"StartNode(n{i})\n"

def relateSuccessorNodes (i : Nat) : String :=
  s!"Successor(n{i}, n{i - 1})\n"

def declareDoneNode (i : Nat) : String :=
  s!"DoneNode(n{i})\n"

def createTransition (i j : Nat) (label : String) : String :=
  let transition := s!"Let t_{i}_{j} := Transition(n{i}, n{j}, {isNeighbor i j})\n"
  let transitionLabel := labelElement s!"t_{i}_{j}" label
  transition ++ transitionLabel

-- This function converts an NFA representation of a regex into a Penrose substance string.
-- It generates nodes, transitions, and labels for the NFA.
-- The nodes are created based on the NFA's structure, and transitions are defined based on
-- the connections between nodes. Labels are applied to nodes and transitions for clarity.
-- The function also handles special cases like done nodes, save nodes, character transitions,
-- epsilon transitions, split nodes, and anchor nodes.
def nfaToSubstance (regex : Regex) : String := Id.run do
  let mut sub := r###"
Let TRUE := True()
Let FALSE := False()
"###
  for i in [0:regex.nfa.nodes.size] do
    sub := sub ++ createNode i
    if i > 0 then sub := sub ++ relateSuccessorNodes i

  sub := sub ++ declareStartNode regex.nfa.start

  for h : i in [0:regex.nfa.nodes.size] do
    let node := regex.nfa.nodes[i]
    match node with
    | .done =>
        sub := sub ++ labelNode i "done"
        sub := sub ++ declareDoneNode i
    | .save pos next =>
        sub := sub ++ labelNode i s!"save {pos} {next}"
        sub := sub ++ createTransition i next epsilon
    | .char ch next =>
        sub := sub ++ labelNode i s!"char '{ch}' {next}"
        sub := sub ++ createTransition i next s!"{ch}"
    | .epsilon next =>
        sub := sub ++ labelNode i s!"epsilon {next}"
        sub := sub ++ createTransition i next epsilon
    | .split next₁ next₂ =>
        sub := sub ++ labelNode i s!"split {next₁} {next₂}"
        sub := sub ++ createTransition i next₁ epsilon
        sub := sub ++ createTransition i next₂ epsilon
    | .fail => ()
    | .anchor a next =>
        sub := sub ++ labelNode i s!"anchor {next}"
        sub := sub ++ createTransition i next s!"{Anchor.toString a}"
    | .sparse cs next =>
        sub := sub ++ labelNode i s!"sparse {next}"
        sub := sub ++ createTransition i next s!"{Classes.toString cs}"

  return sub

-- This function generates a Penrose diagram for the NFA representation of a regex.
def mkNFADiagram (regex : Regex) : MetaM Html :=
  return <PenroseDiagram
      embeds={#[]}
      dsl={include_str "NFAPenrose.domain"}
      sty={include_str "NFAPenrose.style"}
      sub={nfaToSubstance regex} />

-- Use this for testing purposes. Sample regexes avauilable in  regex/tests/Test.lean
def sampleRegex : Regex :=
  --re! r##"a|"##
  --re! r##"(?:|a)+"##
  re! r##"[a-zA-Z0-9_]+@[a-zA-Z0-9]+\.[a-zA-Z]{2,}"##
  -- re! r##"\w+"##
  --re! r"\d{4}-\d{2}-\d{2}"
  --re! r##"^\b"##
  --re! r##"^\b$"##
  --re! r##"(?:foo|bar|[A-Z])\b"##
  --re! r##"(?:foo|bar|[A-Z])\B"##


-- Uncomment the following lines to debug issues with the diagram
-- def substance := nfaToSubstance sampleRegex
-- #eval IO.println substance

-- Place your cursor at the end of the following line to see the NFA diagram
#html mkNFADiagram sampleRegex
