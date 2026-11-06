import Mathlib

/-!
# OpenMath semantic registry

The registry is the single place where an OpenMath symbol identity is related
to a Lean interpretation.  It deliberately separates three things:

1. **identity** — the OpenMath symbol (`cd`, `name`) that a rule refers to;
2. **interpretation** — the Lean constant that represents the symbol in a
   given mathematical domain;
3. **justification** — why that interpretation is faithful, at which
   assurance level, and under which definedness restriction.

Lean constants are referenced with double-backtick names, so a misspelt or
nonexistent Mathlib declaration is a compile error rather than a silent
fabrication.  OpenMath symbols are never inferred from Lean names.
-/

namespace OSR

/-- An OpenMath symbol, identified by its content dictionary and name.
The CD base is always the official one, `http://www.openmath.org/cd`. -/
structure OMSymbol where
  cd : String
  name : String
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/-- Official OpenMath content dictionary base. -/
def OMSymbol.cdbase : String := "http://www.openmath.org/cd"

/-- The full URI of an OpenMath symbol. -/
def OMSymbol.uri (s : OMSymbol) : String := s!"{OMSymbol.cdbase}/{s.cd}#{s.name}"

/-- Mathematical domains in which a rule may be certified. -/
inductive Domain where
  | real
  | complex
  /-- Truth values, for the `logic1` connectives (`OSR.Logic`). -/
  | boolean
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Stable key of a domain in exported artifacts. -/
def Domain.key : Domain → String
  | .real => "real"
  | .complex => "complex"
  | .boolean => "boolean"

/-- The OpenMath symbol naming the carrier set of a domain (`setname1`). -/
def Domain.carrier : Domain → OMSymbol
  | .real => ⟨"setname1", "R"⟩
  | .complex => ⟨"setname1", "C"⟩
  | .boolean => ⟨"setname2", "Boolean"⟩

/-- Assurance that a Lean interpretation faithfully represents an OpenMath
symbol.  This is about the *mapping*, not about any rule. -/
inductive Assurance where
  /-- Reviewed by a person against the CD description and properties. -/
  | reviewed
  /-- Reviewed, and the listed semantic obligations are proved in Lean. -/
  | formallyRelated
  /-- Usable, but the correspondence is not fully justified. -/
  | provisional
  /-- No faithful interpretation is available. -/
  | unsupported
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Stable key of an assurance level in exported artifacts. -/
def Assurance.key : Assurance → String
  | .reviewed => "reviewed"
  | .formallyRelated => "formally_related"
  | .provisional => "provisional"
  | .unsupported => "unsupported"

/-- Whether an assurance level is acceptable for certification. -/
def Assurance.certifiable : Assurance → Bool
  | .reviewed | .formallyRelated => true
  | .provisional | .unsupported => false

/-- A pinned OpenMath content dictionary snapshot.  The snapshot files live in
the `OpenSymbolicRules/OpenMath` repository under `cd/`. -/
structure CDRef where
  cd : String
  version : Nat
  revision : Nat
  date : String
  sha256 : String
  deriving Repr, Inhabited

/-- A semantic obligation: a property stated in the content dictionary (a CMP
or FMP) together with the Lean theorem establishing it for the
interpretation.  A handful of properties never characterizes a function; an
obligation is evidence of compatibility, not a definition. -/
structure Obligation where
  /-- The property as stated in the CD (its CMP text). -/
  cmp : String
  /-- The Lean theorem proving it for the interpretation. -/
  theoremName : Lean.Name
  /-- How the Lean statement relates to the CMP when not literally identical. -/
  note : String := ""
  deriving Repr, Inhabited

/-- A Lean interpretation of an OpenMath symbol in one domain. -/
structure Interpretation where
  domain : Domain
  /-- The Lean constant implementing the symbol. -/
  leanConst : Lean.Name
  assurance : Assurance
  /-- Where the OpenMath operation is defined, in prose.  Lean operations are
  total; this records the part of the domain on which the totalized value is
  meaningful.  The machine-checked counterpart is `OSR.Defined`. -/
  definedness : String
  /-- Why the interpretation is faithful. -/
  justification : String
  /-- Lean theorems discharging semantic obligations (e.g. CD properties). -/
  obligations : List Obligation := []
  /-- Known semantic differences that are not resolved. -/
  unresolved : List String := []
  deriving Repr, Inhabited

/-- A registry entry: one OpenMath symbol and its interpretations. -/
structure SymbolEntry where
  symbol : OMSymbol
  /-- Arity as supported by the OSR expression fragment. -/
  arity : Nat
  /-- Restrictions of the OSR fragment relative to the CD symbol. -/
  fragment : String := ""
  interpretations : List Interpretation
  deriving Repr, Inhabited

/-- The interpretation of an entry in a domain, if any. -/
def SymbolEntry.interpretation? (e : SymbolEntry) (d : Domain) : Option Interpretation :=
  e.interpretations.find? (·.domain == d)

end OSR
