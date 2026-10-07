use makefile_lossless::MakefileVariant;

const VARIANTS: [MakefileVariant; 4] = [
    MakefileVariant::GNUMake,
    MakefileVariant::BSDMake,
    MakefileVariant::NMake,
    MakefileVariant::POSIXMake,
];

/// The make variant chosen by `selector`, with `None` for the default,
/// lenient parser. A seed starting with a newline uses the default parser.
#[allow(dead_code)]
pub fn optional_variant(selector: u8) -> Option<MakefileVariant> {
    match usize::from(selector) % (VARIANTS.len() + 1) {
        0 => None,
        n => Some(VARIANTS[n - 1]),
    }
}

/// Split the input into a make variant, chosen by its first byte as for
/// [`optional_variant`], and the rest as UTF-8 text.
#[allow(dead_code)]
pub fn optional_variant_and_text(data: &[u8]) -> Option<(Option<MakefileVariant>, &str)> {
    let (&selector, rest) = data.split_first()?;
    Some((optional_variant(selector), std::str::from_utf8(rest).ok()?))
}

/// Like [`optional_variant_and_text`], for APIs that require a variant.
#[allow(dead_code)]
pub fn variant_and_text(data: &[u8]) -> Option<(MakefileVariant, &str)> {
    let (&selector, rest) = data.split_first()?;
    let variant = VARIANTS[usize::from(selector) % VARIANTS.len()];
    Some((variant, std::str::from_utf8(rest).ok()?))
}

/// Parse `text` as `variant`, or with the default parser for `None`.
#[allow(dead_code)]
pub fn parse(
    text: &str,
    variant: Option<MakefileVariant>,
) -> makefile_lossless::Parse<makefile_lossless::Makefile> {
    match variant {
        Some(variant) => makefile_lossless::Makefile::parse_with_variant(text, variant),
        None => makefile_lossless::Makefile::parse(text),
    }
}
