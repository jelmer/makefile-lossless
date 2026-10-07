use super::*;

/// The range of the spaces indenting the line `line_range` of `text`, if
/// any.
fn space_indent_range(text: &str, line_range: rowan::TextRange) -> Option<rowan::TextRange> {
    let line = &text[line_range];
    let spaces = line.len() - line.trim_start_matches(' ').len();
    (spaces > 0)
        .then(|| rowan::TextRange::at(line_range.start(), rowan::TextSize::from(spaces as u32)))
}

/// Set the line range and space indent range of `error` in `text`, given
/// the ranges of the line endings that end its logical lines.
pub(crate) fn locate_error_line(
    line_ends: &[rowan::TextRange],
    text: &str,
    error: &mut PositionedParseError,
) {
    // The first line ending after the start of the error.
    let i = line_ends.partition_point(|end| end.end() <= error.range.start());
    let start = i.checked_sub(1).map_or(0.into(), |i| line_ends[i].end());
    let end = line_ends
        .get(i)
        .map_or(rowan::TextSize::of(text), |end| end.start());
    error.line_range = rowan::TextRange::new(start, end);
    error.space_indent_range = if error.kind == ParseErrorKind::MissingSeparator {
        space_indent_range(text, error.line_range)
    } else {
        None
    };
}

impl Parser<'_> {
    pub(super) fn error(&mut self, kind: ParseErrorKind, msg: String) {
        self.builder.start_node(ERROR.into());
        self.record_error(kind, msg);
        if self.current().is_some() {
            self.bump();
        }
        self.builder.finish_node();
    }

    /// Record an error without consuming the current token.
    pub(super) fn record_error(&mut self, kind: ParseErrorKind, msg: String) {
        let range = self.current_range();
        let line = self.line_at(range.start());
        debug_assert!(
            self.current() != Some(INDENT) || kind == ParseErrorKind::RecipeBeforeFirstTarget,
            "{kind:?} error at the indent of the next line"
        );
        self.push_error(kind, msg, range, line);
    }

    /// Record an error for a block that is still open at the end of the
    /// input. Like GNU and BSD make, report it on the line after the
    /// last one, even if the input does not end with a newline.
    pub(super) fn record_unterminated_error(&mut self, kind: ParseErrorKind, msg: String) {
        let range = self.current_range();
        // The number of lines, as counted by `str::lines`.
        let lines = self.line_starts.len()
            - usize::from(self.original_text.is_empty() || self.original_text.ends_with('\n'));
        self.push_error(kind, msg, range, lines + 1);
    }

    /// The 1-based line number of `offset`.
    pub(super) fn line_at(&self, offset: rowan::TextSize) -> usize {
        self.line_starts
            .partition_point(|&start| start <= usize::from(offset))
    }

    pub(super) fn push_error(
        &mut self,
        kind: ParseErrorKind,
        message: String,
        range: rowan::TextRange,
        line: usize,
    ) {
        let context = self.get_context_for_line(line);
        self.errors.push(ErrorInfo {
            message: message.clone(),
            line,
            context,
            kind,
        });

        self.positioned_errors.push(PositionedParseError {
            message,
            range,
            code: None,
            kind,
            // Set by `Parser::parse` once all lines have been seen.
            line_range: rowan::TextRange::empty(range.start()),
            space_indent_range: None,
        });
    }

    /// The text of the given 1-based line, without its line ending.
    fn get_context_for_line(&self, line_number: usize) -> String {
        let Some(&start) = self.line_starts.get(line_number - 1) else {
            return String::new();
        };
        let line = match self.line_starts.get(line_number) {
            Some(&next) => {
                let line = &self.original_text[start..next - 1];
                line.strip_suffix('\r').unwrap_or(line)
            }
            None => &self.original_text[start..],
        };
        line.to_string()
    }
}
