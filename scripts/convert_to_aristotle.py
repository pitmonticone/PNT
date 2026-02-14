#!/usr/bin/env python3
"""
Convert Lean files with Architect/blueprint annotations to Aristotle-compatible format.

This script:
1. Removes the 'import Architect' line
2. Converts 'blueprint_comment' blocks to standard Lean doc comments (/-! ... -/)
3. Converts @[blueprint ...] attributes to docstrings with the template:

   /-- **title**

   statement

   PROVIDED SOLUTION:
   proof
   -/

4. Converts completed proofs (sorry-free) to use 'admit' so Aristotle ignores them
5. Leaves 'sorry' proofs as-is so Aristotle focuses on proving them

Usage:
    python convert_to_aristotle.py input.lean [output.lean]

If output.lean is not specified, the input file is modified in place.
"""

import re
import sys
from pathlib import Path


def extract_blueprint_content(text: str) -> tuple[str, str, str, str]:
    """
    Extract title, statement, proof from a @[blueprint ...] block.
    Returns (title, statement, proof, discussion_id).
    """
    title = ""
    statement = ""
    proof = ""
    discussion = ""

    title_match = re.search(r'\(title\s*:=\s*"([^"]+)"\)', text)
    if title_match:
        title = title_match.group(1)

    statement_match = re.search(r'\(statement\s*:=\s*/--\s*(.*?)\s*-/\)', text, re.DOTALL)
    if statement_match:
        statement = statement_match.group(1).strip()

    proof_match = re.search(r'\(proof\s*:=\s*/--\s*(.*?)\s*-/\)', text, re.DOTALL)
    if proof_match:
        proof = proof_match.group(1).strip()

    discussion_match = re.search(r'\(discussion\s*:=\s*(\d+)\)', text)
    if discussion_match:
        discussion = discussion_match.group(1)

    return title, statement, proof, discussion


def convert_latex_to_markdown(text: str) -> str:
    """Convert LaTeX-style formatting to markdown-friendly format."""
    text = re.sub(r'(^|\s)\\\[', r'\1$$', text, flags=re.MULTILINE)
    text = re.sub(r'\\\](\s|$|\.)', r'$$\1', text, flags=re.MULTILINE)
    text = re.sub(r'\\begin\{equation\}(?:\\label\{[^}]+\})?', '$$', text)
    text = re.sub(r'\\end\{equation\}', '$$', text)
    text = re.sub(r'\\ref\{lem:([^}]+)\}', r'`lemma_\1`', text)
    text = re.sub(r'\\ref\{prop:([^}]+)\}', r'`proposition_\1`', text)
    text = re.sub(r'\\ref\{eq:([^}]+)\}', r'(equation \1)', text)
    text = re.sub(r'Lemma~?\\ref\{lem:([^}]+)\}', r'`lemma_\1`', text)
    text = re.sub(r'Proposition~?\\ref\{prop:([^}]+)\}', r'`proposition_\1`', text)
    text = re.sub(r'\{\\em\s+([^}]+)\}', r'*\1*', text)
    text = re.sub(r'\\label\{[^}]+\}', '', text)
    text = re.sub(r'\\eqref\{([^}]+)\}', r'(equation \1)', text)
    text = re.sub(r'\\cite\[[^\]]+\]\{[^}]+\}', '[reference]', text)
    text = re.sub(r'\\cite\{[^}]+\}', '[reference]', text)
    text = re.sub(r'\\footnote\{([^}]+)\}', r' (\1)', text)
    text = re.sub(r'\\url\{([^}]+)\}', r'\1', text)
    text = text.replace(r'\S ', '§')
    return text


def create_docstring(title: str, statement: str, proof: str) -> str:
    """Create a docstring in the target format. Returns empty string if no content."""
    # If there's no content, don't create a docstring
    if not title and not statement and not proof:
        return ""

    parts = []
    if title:
        parts.append(f"/-- **{title}**")
        if statement:
            statement = convert_latex_to_markdown(statement)
            parts.append("")
            parts.append(statement)
    elif statement:
        statement = convert_latex_to_markdown(statement)
        parts.append(f"/-- {statement}")
    if proof:
        proof = convert_latex_to_markdown(proof)
        parts.append("")
        parts.append("PROVIDED SOLUTION:")
        parts.append(proof)
    parts.append("-/")
    return "\n".join(parts)


def convert_blueprint_comment(match: re.Match) -> str:
    """Convert a blueprint_comment block to a module docstring."""
    content = match.group(1).strip()

    section_match = re.match(r'\\(sub)?section\{([^}]+)\}', content)
    if section_match:
        is_subsection = section_match.group(1) is not None
        section_title = section_match.group(2)
        header = "##" if is_subsection else "#"
        remaining = content[section_match.end():].strip()
        result = f"/-!\n{header} {section_title}\n"
        if remaining:
            remaining = convert_latex_to_markdown(remaining)
            result += f"\n{remaining}\n"
        result += "-/"
        return result

    if content.startswith("\\begin{remark}"):
        content = content.replace("\\begin{remark}", "").replace("\\end{remark}", "").strip()
        content = convert_latex_to_markdown(content)
        return f"/-!\n**Remark:** {content}\n-/"

    content = convert_latex_to_markdown(content)
    return f"/-!\n{content}\n-/"


def is_new_top_level_start(line: str) -> bool:
    """Check if a line starts a new top-level declaration."""
    if not line or line[0] in ' \t':
        return False
    stripped = line.strip()
    # Check for 'local notation' specifically first
    if stripped.startswith('local notation'):
        return True
    # Check for single-line comments at the start (non-indented)
    # These indicate we've left the proof body
    if stripped.startswith('--'):
        return True
    # Check for block comments (/-) at the start (non-indented)
    # These indicate we've left the proof body
    if stripped.startswith('/-'):
        return True
    return bool(re.match(
        r'^(private\s+|local\s+)?(noncomputable\s+)?(theorem|lemma|def|abbrev|instance|example|'
        r'structure|class|inductive|@\[|end\s|open\s|section\s|namespace\s|variable\s|omit\s)',
        stripped
    ))


def find_proof_end(lines: list[str], start_idx: int) -> int:
    """
    Find the end of a proof starting from start_idx.
    Returns the index of the last line of the proof.
    """
    i = start_idx + 1
    while i < len(lines):
        line = lines[i]
        if is_new_top_level_start(line):
            return i - 1
        i += 1
    return len(lines) - 1


def convert_inline_by_proofs(content: str) -> str:
    """
    Convert inline 'by' proofs (not ':= by') to 'by admit'.
    This handles Prop-valued fields in structures/defs that use tactic proofs.
    Examples:
      h2 := by simpa [foo] using bar  ->  h2 := by admit
      (by simp [one_add_one_eq_two])  ->  (by admit)
      integrable k hk := by
        have hf : ...
        simpa ...                      ->  integrable k hk := by admit

    IMPORTANT: This function should NOT modify content inside comments or docstrings.
    """
    lines = content.split('\n')
    result_lines = []
    i = 0
    in_comment = False  # Track whether we're inside a block comment or docstring

    while i < len(lines):
        line = lines[i]

        # Track block comments and docstrings
        # Check for start of block comment/docstring
        if '/-' in line and not in_comment:
            # Check if comment starts and ends on same line
            if '-/' in line and line.index('-/') > line.index('/-'):
                # Single-line comment, don't set in_comment
                pass
            else:
                in_comment = True
        # Check for end of block comment/docstring
        if '-/' in line and in_comment:
            in_comment = False
            result_lines.append(line)
            i += 1
            continue

        # If inside a comment, don't modify the line
        if in_comment:
            result_lines.append(line)
            i += 1
            continue

        # Check if this line has ':= by' that's indented (part of a where block)
        # Skip lines that look like they're part of lemma/theorem signature continuations
        # These have ':= by' but are continuations of multi-line signatures
        if ':= by' in line:
            stripped = line.strip()
            # Skip if this is a top-level declaration
            if stripped.startswith(('theorem ', 'lemma ', '@[', 'private theorem', 'private lemma')):
                result_lines.append(line)
                i += 1
                continue
            # Skip if this looks like a lemma signature continuation (ends with := by)
            # These are lines that end with ':= by' (possibly with trailing spaces) and are
            # typically the last line of a multi-line type signature.
            # BUT: Don't skip if this is a field in a where block (field_name ... := by)
            # Heuristic: top-level signature continuations usually have type annotations with ':'
            # before the ':=' (e.g., "    (h : Foo) : Bar := by")
            # Fields in where blocks typically have pattern like "field_name arg1 arg2 := by"
            # without a return type annotation before :=
            if stripped.endswith(':= by') or stripped == ':= by':
                # Check if this is part of a top-level theorem/lemma declaration
                # by looking back in result_lines for a theorem/lemma declaration line
                # If so, the proof was already handled by convert_completed_proofs_to_admit
                is_top_level_continuation = False
                for k in range(len(result_lines) - 1, max(0, len(result_lines) - 50), -1):
                    prev_line = result_lines[k]
                    if not prev_line.strip():
                        continue
                    # If we hit a non-indented, non-comment line, check if it's a theorem/lemma
                    if prev_line and prev_line[0] not in ' \t':
                        if re.match(r'^(@\[.*?\]\s*)?(private\s+)?(noncomputable\s+)?(theorem|lemma)\s', prev_line):
                            is_top_level_continuation = True
                        break
                    # Docstring closing - keep looking back
                    if prev_line.strip() == '-/':
                        continue
                if is_top_level_continuation:
                    result_lines.append(line)
                    i += 1
                    continue
                # Fall through to handle it as a field in a where block
            # Check if this is an indented line (part of a where block or structure)
            if line and line[0] in ' \t':
                by_pos = line.find(':= by')

                # Check if ':= by' is inside parentheses (default argument value)
                # If so, this is not a proof we should modify
                prefix = line[:by_pos]
                paren_depth = prefix.count('(') - prefix.count(')')
                if paren_depth > 0:
                    # This is a default argument inside a signature, not a proof
                    result_lines.append(line)
                    i += 1
                    continue

                after_by = line[by_pos + 5:].strip()

                # Case 1: Single-line proof (something after 'by' on same line)
                if after_by and after_by != 'admit':
                    if 'sorry' not in after_by:
                        line = line[:by_pos + 5] + ' admit'
                    result_lines.append(line)
                    i += 1
                    continue

                # Case 2: Multi-line proof (nothing after 'by', or just whitespace)
                # We need to find the end of this proof block and skip it
                if not after_by:
                    # Check if the next line is just 'admit' - if so, this was already converted
                    if i + 1 < len(lines) and lines[i + 1].strip() == 'admit':
                        # Already converted by convert_completed_proofs_to_admit, skip both lines
                        result_lines.append(line)
                        result_lines.append(lines[i + 1])
                        i += 2
                        continue

                    # Get the indentation level of this field
                    field_indent = len(line) - len(line.lstrip())

                    # Skip all continuation lines that are more indented than the field
                    j = i + 1
                    while j < len(lines):
                        next_line = lines[j]
                        # Empty lines are part of the proof
                        if not next_line.strip():
                            j += 1
                            continue
                        # Check indentation - if less or equal to field indent, we're done
                        next_indent = len(next_line) - len(next_line.lstrip())
                        if next_indent <= field_indent:
                            break
                        j += 1

                    # Check if the proof contains 'sorry'
                    proof_body = '\n'.join(lines[i:j])
                    if 'sorry' not in proof_body:
                        # Replace with single-line 'by admit'
                        result_lines.append(line[:by_pos + 5] + ' admit')
                        # Add blank line if the next non-empty line is a new declaration
                        if j < len(lines) and lines[j].strip() and not lines[j].strip().startswith(('|', '·', '-', '}')):
                            result_lines.append('')
                    else:
                        # Keep the proof as-is
                        for k in range(i, j):
                            result_lines.append(lines[k])

                    i = j
                    continue

        # Pattern 2: (by <tactics>) inline - commonly used in term-mode proofs
        # e.g., (by simp [one_add_one_eq_two])
        # But skip if already (by admit) or contains sorry
        def replace_by_parens(m):
            inner = m.group(1)
            if inner.strip() == 'admit' or 'sorry' in inner:
                return m.group(0)
            return '(by admit)'

        line = re.sub(r'\(by\s+([^)]+)\)', replace_by_parens, line)

        result_lines.append(line)
        i += 1

    return '\n'.join(result_lines)


def convert_completed_proofs_to_admit(content: str) -> str:
    """
    Convert completed top-level theorem/lemma proofs (those without 'sorry') to use 'admit'.
    Leave proofs with 'sorry' unchanged so Aristotle focuses on them.
    Handles both tactic-mode (:= by) and term-mode (:=) proofs.
    """
    lines = content.split('\n')
    result_lines = []
    i = 0

    while i < len(lines):
        line = lines[i]

        # Check for 'omit ... in' prefix before theorem/lemma
        omit_line = None
        if line.startswith('omit ') and (line.rstrip().endswith(' in') or line.rstrip() == 'omit in'):
            if i + 1 < len(lines):
                next_line = lines[i + 1]
                if (next_line.startswith('theorem ') or next_line.startswith('lemma ') or
                    next_line.startswith('private theorem ') or next_line.startswith('private lemma ') or
                    next_line.startswith('@[simp] theorem ') or next_line.startswith('@[simp] lemma ') or
                    re.match(r'^@\[.*\]\s*(theorem|lemma)\s', next_line)):
                    omit_line = line
                    i += 1
                    line = lines[i]

        # Match theorem/lemma declarations, including those with attributes like @[simp]
        decl_match = re.match(r'^(@\[.*?\]\s*)?(private\s+)?(theorem|lemma)\s', line)
        if decl_match:
            decl_start = i
            theorem_start = i

            # Find the line containing ':= by' or ':=' for the TOP-LEVEL declaration
            j = theorem_start
            by_line_idx = -1
            term_mode_line_idx = -1
            # Track cumulative parenthesis depth across lines for multi-line signatures
            cumulative_paren_depth = 0

            while j < len(lines):
                current_line = lines[j]

                # If we hit a new top-level declaration, the theorem doesn't have := by
                if j > theorem_start and is_new_top_level_start(current_line):
                    break

                stripped = current_line.strip()

                # Check if this line is a 'have' or 'let' statement in the type signature
                # These can contain ':= by' or ':=' but are not the main proof
                # They are indented continuation lines that provide auxiliary definitions
                is_signature_have_or_let = (
                    current_line and current_line[0] in ' \t' and  # indented
                    (stripped.startswith('have ') or stripped.startswith('let '))
                )

                if ':= by' in current_line:
                    # Check if this is a 'have' or 'let' inside the type signature
                    if is_signature_have_or_let:
                        # This is a have/let in the type signature, not the proof
                        # Update paren depth and continue
                        cumulative_paren_depth += current_line.count('(') - current_line.count(')')
                        j += 1
                        continue
                    # Check if ':= by' is inside parentheses (default argument value)
                    # Count parentheses to determine if we're inside a default argument
                    # A ':= by' that starts the proof should not be inside parentheses
                    # Need to account for cumulative depth from previous lines + depth up to ':= by'
                    by_pos = current_line.find(':= by')
                    prefix = current_line[:by_pos]
                    local_paren_depth = prefix.count('(') - prefix.count(')')
                    total_paren_depth = cumulative_paren_depth + local_paren_depth
                    if total_paren_depth > 0:
                        # ':= by' is inside parentheses - it's a default argument, not the proof
                        # Update cumulative depth for the whole line and continue
                        cumulative_paren_depth += current_line.count('(') - current_line.count(')')
                        j += 1
                        continue
                    # Found ':= by' - this marks start of tactic proof
                    by_line_idx = j
                    break

                # Check for term-mode definition (has := but not := by)
                if ':=' in current_line and ':= by' not in current_line:
                    # Skip if this is a have/let in the type signature
                    if is_signature_have_or_let:
                        cumulative_paren_depth += current_line.count('(') - current_line.count(')')
                        j += 1
                        continue
                    # Check this is not inside a let or fun binding
                    # 'let ... :=' can appear anywhere in a type signature
                    if not stripped.startswith('let ') and not stripped.startswith('fun '):
                        # Also check if 'let ... :=' appears anywhere in the line (inside type signature)
                        if not re.search(r'\blet\s+\w+\s*:=', current_line):
                            # Check if := is a named argument inside parentheses like (s := s)
                            # Named arguments have pattern: (name := value) or (name := ...)
                            # We should skip these
                            if not re.search(r'\(\s*\w+\s*:=', current_line):
                                # Check if := is inside parentheses (default argument value)
                                eq_pos = current_line.find(':=')
                                prefix = current_line[:eq_pos]
                                local_paren_depth = prefix.count('(') - prefix.count(')')
                                total_paren_depth = cumulative_paren_depth + local_paren_depth
                                if total_paren_depth <= 0:
                                    # This is a term-mode proof
                                    term_mode_line_idx = j
                                    break

                # Update cumulative paren depth for this line
                cumulative_paren_depth += current_line.count('(') - current_line.count(')')
                j += 1

            # Handle term-mode proofs
            if term_mode_line_idx != -1:
                # Find the end of the term-mode proof
                proof_end = find_proof_end(lines, term_mode_line_idx)

                # Extract the full proof body
                proof_body = '\n'.join(lines[decl_start:proof_end + 1])

                # Check if proof contains 'sorry'
                has_sorry = bool(re.search(r'\bsorry\b', proof_body))

                if has_sorry:
                    # Keep proof as-is
                    if omit_line:
                        result_lines.append(omit_line)
                    for k in range(decl_start, proof_end + 1):
                        result_lines.append(lines[k])
                else:
                    # Replace term-mode proof with 'by admit'
                    # Find where := is and replace everything after it
                    term_line = lines[term_mode_line_idx]
                    eq_pos = term_line.find(':=')
                    # Output omit line if present
                    if omit_line:
                        result_lines.append(omit_line)
                    # Output lines from decl_start to term_mode_line_idx-1 (if any)
                    for k in range(decl_start, term_mode_line_idx):
                        result_lines.append(lines[k])
                    # Output the line with := by admit
                    result_lines.append(term_line[:eq_pos] + ':= by')
                    result_lines.append('  admit')

                # Add a blank line after the declaration if there isn't one
                if proof_end + 1 < len(lines) and lines[proof_end + 1].strip():
                    result_lines.append('')

                i = proof_end + 1
                continue

            if by_line_idx == -1:
                # No ':= by' or term-mode proof found for this declaration, output as-is
                if omit_line:
                    result_lines.append(omit_line)
                result_lines.append(line)
                i += 1
                continue

            # Found ':= by' - now find the end of the proof
            proof_end = find_proof_end(lines, by_line_idx)

            # Extract the full proof body
            proof_body = '\n'.join(lines[decl_start:proof_end + 1])

            # Check if proof contains 'sorry'
            has_sorry = bool(re.search(r'\bsorry\b', proof_body))

            if has_sorry:
                # Keep proof as-is
                if omit_line:
                    result_lines.append(omit_line)
                for k in range(decl_start, proof_end + 1):
                    result_lines.append(lines[k])
            else:
                # Replace proof body with 'admit'
                # Output omit line if present
                if omit_line:
                    result_lines.append(omit_line)
                # Output lines from decl_start to the line with ':= by'
                # But truncate the ':= by' line to just ':= by' (remove any tactic on same line)
                for k in range(decl_start, by_line_idx):
                    result_lines.append(lines[k])
                # Handle the ':= by' line - truncate everything after ':= by'
                by_line = lines[by_line_idx]
                by_pos = by_line.find(':= by')
                result_lines.append(by_line[:by_pos + 5])  # Include ':= by'
                result_lines.append('  admit')

            # Add a blank line after the declaration if there isn't one
            if proof_end + 1 < len(lines) and lines[proof_end + 1].strip():
                result_lines.append('')

            i = proof_end + 1
        else:
            result_lines.append(line)
            i += 1

    return '\n'.join(result_lines)


def process_file_iterative(content: str) -> str:
    """Process the file iteratively to handle complex nested structures."""
    # Collect PrimeNumberTheoremAnd imports before removing import lines
    project_imports = re.findall(r'^import (PrimeNumberTheoremAnd\..*)$', content, flags=re.MULTILINE)

    # Remove ALL import lines
    content = re.sub(r'^import .*\n', '', content, flags=re.MULTILINE)

    # Build import block: Mathlib + project imports (converted to Aristotle versions)
    import_lines = ['import Mathlib']
    for imp in project_imports:
        # Convert imports to Aristotle versions (e.g., PrimeNumberTheoremAnd.Sobolev -> PrimeNumberTheoremAnd.SobolevAristotle)
        # Handle nested paths like PrimeNumberTheoremAnd.Mathlib.Foo.Bar -> PrimeNumberTheoremAnd.Mathlib.Foo.BarAristotle
        if not imp.endswith('Aristotle'):
            imp = imp + 'Aristotle'
        import_lines.append(f'import {imp}')

    content = '\n'.join(import_lines) + '\n\n' + content.lstrip()

    # Convert blueprint_comment blocks
    content = re.sub(
        r'blueprint_comment\s*/--\s*(.*?)\s*-/',
        convert_blueprint_comment,
        content,
        flags=re.DOTALL
    )

    # Handle @[blueprint ...] attributes
    result = []
    i = 0
    lines = content.split('\n')

    while i < len(lines):
        line = lines[i]

        # Check for 'open ... in' followed by @[blueprint
        open_in_line = None
        if re.match(r'^open\s+.*\s+in\s*$', line):
            # Check if next line is @[blueprint
            if i + 1 < len(lines) and lines[i + 1].strip().startswith('@[blueprint'):
                open_in_line = line
                i += 1
                line = lines[i]

        if line.strip().startswith('@[blueprint'):
            # Remove any preceding orphan docstring (regular /-- ... -/ that would be replaced)
            # Look back and remove docstrings that aren't module docs (/-! ... -/)
            # IMPORTANT: Only remove actual docstrings (/--), not block comments (/-)
            while result and result[-1].strip() == '':
                result.pop()  # Remove trailing blank lines
            # Check if the last non-empty item is a regular docstring
            if result:
                last_item = result[-1]
                # Check if it's a single-line regular docstring (starts with /-- and ends with -/)
                # but not a module docstring (which starts with /-!)
                stripped = last_item.strip()
                if stripped.startswith('/--') and stripped.endswith('-/'):
                    result.pop()  # Remove the orphan docstring
                elif stripped.endswith('-/') and not stripped.startswith('/-'):
                    # Multi-line docstring case - look back for /--
                    # (the ending line doesn't start with /-, so it's a continuation)
                    j = len(result) - 1
                    while j >= 0:
                        line_j = result[j].strip()
                        if line_j.startswith('/--'):
                            # Found start of docstring, remove from here to end
                            result = result[:j]
                            break
                        elif line_j.startswith('/-'):
                            # It's a module docstring or block comment, don't remove
                            break
                        j -= 1

            blueprint_lines = [line]
            # Remove docstring content before counting brackets (docstrings can contain [] in LaTeX)
            line_for_counting = re.sub(r'/--.*?-/', '', line)
            bracket_count = line_for_counting.count('[') - line_for_counting.count(']')
            in_docstring = False

            i += 1
            while i < len(lines) and (bracket_count > 0 or in_docstring):
                current_line = lines[i]
                blueprint_lines.append(current_line)

                # Track docstring state and determine if we should count brackets
                was_in_docstring = in_docstring
                if '/--' in current_line and '-/' not in current_line:
                    # Docstring starts on this line and doesn't end on this line
                    in_docstring = True
                elif '-/' in current_line and in_docstring:
                    # Docstring ends on this line
                    in_docstring = False

                # Count brackets based on docstring state
                has_docstring_start = '/--' in current_line
                has_docstring_end = '-/' in current_line

                if was_in_docstring:
                    # We were inside a multi-line docstring
                    if has_docstring_end:
                        # Docstring ends on this line - count brackets AFTER the -/
                        close_pos = current_line.find('-/')
                        after_docstring = current_line[close_pos + 2:]
                        bracket_count += after_docstring.count('[') - after_docstring.count(']')
                    # If docstring continues, don't count any brackets
                elif has_docstring_start and has_docstring_end:
                    # Single-line docstring - remove it and count remaining brackets
                    line_for_counting = re.sub(r'/--.*?-/', '', current_line)
                    bracket_count += line_for_counting.count('[') - line_for_counting.count(']')
                elif has_docstring_start:
                    # Docstring starts but doesn't end - count brackets BEFORE the /--
                    start_pos = current_line.find('/--')
                    before_docstring = current_line[:start_pos]
                    bracket_count += before_docstring.count('[') - before_docstring.count(']')
                else:
                    # No docstring on this line - count brackets directly
                    bracket_count += current_line.count('[') - current_line.count(']')

                i += 1

            blueprint_text = '\n'.join(blueprint_lines)
            title, statement, proof, _ = extract_blueprint_content(blueprint_text)
            docstring = create_docstring(title, statement, proof)
            # If there was an 'open ... in' before @[blueprint, preserve it
            if open_in_line:
                result.append(open_in_line)
            # Only append docstring if it has content
            if docstring:
                result.append(docstring)
            # The lines starting at index i are the declaration (theorem/lemma) that follows the @[blueprint]
            # We need to include all lines until the next top-level declaration or end of theorem
            # Multi-line declarations continue until we hit ':= by' or ':=' followed by a proof
            while i < len(lines):
                decl_line = lines[i]
                result.append(decl_line)
                i += 1
                # Check if this line completes the declaration signature
                # (contains ':= by' for tactic proofs or ':=' followed by term-mode proof start)
                if ':= by' in decl_line or (':=' in decl_line and ':= by' not in decl_line):
                    break
                # Also break if we hit a blank line (declaration with no proof body yet)
                if not decl_line.strip():
                    break
                # Or if the next line starts a new top-level declaration
                if i < len(lines) and is_new_top_level_start(lines[i]):
                    break
        else:
            result.append(line)
            i += 1

    content = '\n'.join(result)

    # Convert completed proofs to admit
    content = convert_completed_proofs_to_admit(content)

    # Convert inline by proofs (in defs, structures, etc.) to admit
    content = convert_inline_by_proofs(content)

    return content


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    input_path = Path(sys.argv[1])

    # If output not specified, create NameAristotle.lean from Name.lean
    if len(sys.argv) > 2:
        output_path = Path(sys.argv[2])
    else:
        stem = input_path.stem
        if stem.endswith('Aristotle'):
            output_path = input_path  # Already an Aristotle file, modify in place
        else:
            output_path = input_path.parent / f"{stem}Aristotle.lean"

    if not input_path.exists():
        print(f"Error: Input file '{input_path}' does not exist.")
        sys.exit(1)

    content = input_path.read_text(encoding='utf-8')
    converted = process_file_iterative(content)
    output_path.write_text(converted, encoding='utf-8')

    print(f"Converted '{input_path}' -> '{output_path}'")


if __name__ == "__main__":
    main()
