" Vim syntax file
" Language:        Lambdapi
" Maintainer:      Rodolphe Lepigre <rodolphe.lepigre@inria.fr>
" Last Change:     12/09/2018
" Version:         1.0
" Original Author: Rodolphe Lepigre <rodolphe.lepigre@inria.fr>

if exists("b:current_syntax")
  finish
endif

" Single-line comments.
syntax keyword Todo contained TODO FIXME NOTE
syntax region Comment start="//\($\|[^/]\)" end="$" contains=Todo

" Documentation comments (FIXME).
syntax include @markdown syntax/markdown.vim
syntax region Comment start="///" end="$" contains=@markdown

" Natural number.
syntax match NaturalNumber "\<\([0]\|\([1-9][0-9]*\)\)\>"
highlight link NaturalNumber PreProc


" Keywords.
syntax keyword KeywordOK contained require open as let in
syntax keyword KeywordOK contained symbol const injective
syntax keyword KeywordOK contained rule and definition theorem
syntax keyword KeywordOK contained assert assertnot set
syntax keyword KeywordOK contained proof qed admit abort refine intro
syntax keyword KeywordOK contained apply simpl rewrite focus print
highlight link KeywordOK Keyword

" Keyword in identifier.
syntax keyword KeywordKO contained require open as let in
syntax keyword KeywordKO contained symbol const injective
syntax keyword KeywordKO contained rule and definition theorem
syntax keyword KeywordKO contained assert assertnot set
syntax keyword KeywordKO contained proof qed admit abort refine intro
syntax keyword KeywordKK contained apply simpl rewrite focus print
highlight link KeywordKO Error

" Escaped identifiers member.
syntax region EscapedIdentifier contained matchgroup=Identifier start="{|" end="|}"
highlight link EscapedIdentifier String

" Normal identifiers member.
syntax match IdentifierNotKeyword "\<\h\w*\>" contained contains=KeywordKO
syntax match IdentifierOrAKeyword "\<\h\w*\>" contained contains=KeywordOK
"highlight link NormalIdentifier Identifier

" Qualified identifiers.
syntax match Identifier
  \ "\(\(\<\h\w*\>\|\({|\([^|]\|\n\|\(|[^}]\)\)*|*|}\)\)\.\)\+\(\<\h\w*\>\|\({|\([^|]\|\n\|\(|[^}]\)\)*|*|}\)\)"
  \ contains=EscapedIdentifier,IdentifierNotKeyword

" Non-qualified identifier (or keyword).
syntax match Identifier
  \ "\(\<\h\w*\>\|\({|\([^|]\|\n\|\(|[^}]\)\)*|*|}\)\)\.\@!"
  \ contains=EscapedIdentifier,IdentifierOrAKeyword

" Special symbols.
syntax match Keyword "("
syntax match Keyword ")"
syntax match Keyword "\["
syntax match Keyword "\]"
syntax match Keyword ":"
syntax match Keyword "⇒"
syntax match Keyword "→"
syntax match Keyword "∀"
syntax match Keyword "λ"
syntax match Keyword "≔"
syntax match Keyword ","
syntax match Keyword ";"
syntax match Keyword "_"
syntax match Keyword "="

" Other special classes.
syntax match Type "\u\w*"
syntax match Constant "&\(\<\h\w*\>\|\({|\([^|]\|\(|[^}]\)\)*|*|}\)\)"
syntax match PreProc  "?\(\<\h\w*\>\|\({|\([^|]\|\(|[^}]\)\)*|*|}\)\)"

" Abbreviations.
abbreviate -> →
abbreviate => ⇒
abbreviate !  ∀
abbreviate (! (∀
abbreviate := ≔
abbreviate \  λ
abbreviate (\ (λ
