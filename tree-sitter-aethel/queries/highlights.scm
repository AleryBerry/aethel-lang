; Keywords
[
  "as"
  "let"
  "panic"
  "todo"
  "use"
  "law"
  "preserves"
  "when"
  "always"
  "never"
  "decreases"
  "extern"
] @keyword

"type" @keyword.type

; Function Keywords
"fn" @keyword.function

; Imports
"import" @keyword.import

; Conditionals
[
  "case"
  "if"
  "else"
] @keyword.conditional

; Loops
[
  "for"
  "in"
  "while"
] @keyword.repeat

; Return
"return" @keyword.return

; Concurrency & Views
[
  "view"
  "fork"
  "join"
] @keyword.coroutine

; Type & Ownership Qualifiers
[
  "const"
  "move"
  (opacity_modifier)
  (visibility_modifier)
  (mutable_modifier)
  (borrow_mode)
] @keyword.modifier

; Attributes (`@layout(aosoa(8))`)
(attribute
  "@" @attribute
  name: (_) @attribute)

(attribute
  arguments: (arguments
    (argument
      value: (identifier) @attribute.builtin)))

(attribute
  arguments: (arguments
    (argument
      value: (function_call
        function: (identifier) @attribute.builtin))))

; Punctuation
[
  "("
  ")"
  "["
  "]"
  "{"
  "}"
] @punctuation.bracket

[
  ","
  "."
  ":"
  ";"
  "->"
  "=>"
  "<-"
] @punctuation.delimiter

[
  "@"
  "?"
] @punctuation.special

; Operators
[
  "%"
  "%="
  "&"
  "&&"
  "*"
  "*="
  "*%"
  "*|"
  "+"
  "+="
  "+%"
  "+|"
  "-"
  "-="
  "-%"
  "-|"
  ".."
  "..="
  "/"
  "/="
  "<"
  "<<"
  "<="
  "<>"
  "="
  "=="
  "!="
  "!"
  "~"
  "~>"
  ">"
  ">="
  ">>"
  "|"
  "|>"
  "||"
  "^"
] @operator

; Identifiers
(identifier) @variable

; Comments
(comment) @comment @spell

[
  (module_comment)
  (statement_comment)
] @comment.documentation @spell

; Unused Identifiers
[
  (discard)
  (hole)
] @comment

; Modules & Imports
(module) @module

(import_declaration
  alias: (_) @module)

(remote_type_identifier
  module: (identifier) @module)

(unqualified_import
  name: (_) @function)

; Strings
(string) @string

; Numbers & Booleans
(integer) @number
(float) @number.float
(boolean) @boolean

; Function Parameter Labels & Parameters
(function_call
  arguments: (arguments
    (argument
      label: (label) @label)))

(function_parameter
  label: (label)? @label
  name: (identifier) @variable.parameter)

(mutable_pattern
  name: (identifier) @variable)

; Records & Field Access
(record_field
  name: (label) @variable.member)

(record_field_init
  label: (label) @variable.member)

(record_pattern_argument
  label: (label) @variable.member)

(field_access
  field: (label) @variable.member)

(field_path
  (identifier) @variable.member)

(data_constructor_argument
  label: (label) @variable.member)

; Types
(primitive_type) @type.builtin

(int_range_type
  "Int" @type.builtin)

[
  (type_identifier)
  (type_parameter)
  (type_var)
] @type

([
  (type_identifier)
  (constructor_name)
] @type.builtin
  (#any-of? @type.builtin "Collection" "View" "Option" "Result" "String" "Exclusive" "Shared"))

; Tuples
(tuple_access
  index: (integer) @operator)

; Functions & Laws
(function
  name: (identifier) @function)

(law_declaration
  name: (identifier) @function)

(function_call
  function: (identifier) @function.call)

(function_call
  function: (field_access
    field: (label) @function.call))

(external_function
  name: (identifier) @function)

(extern_member_fn
  name: (identifier) @function)

(view_expression
  name: (identifier) @variable)

; Constructors
(constructor_name) @type @constructor

([
  (type_identifier)
  (constructor_name)
] @constant.builtin
  (#any-of? @constant.builtin "Ok" "Err" "Error" "Some" "None"))

; Pipe Operator
(binary_expression
  operator: "|>"
  right: (identifier) @function.call)
