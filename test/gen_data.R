

gen.data <- function(object, file.root) {
    saveRDS(object=object, paste0(file.root,".bin.rds"), ascii=FALSE, compress=FALSE)
    saveRDS(object=object, paste0(file.root,".txt.rds"), ascii=TRUE, compress=FALSE)
    saveRDS(object=object, paste0(file.root,".rds"), ascii=FALSE, compress=TRUE)
}

# see https://github.com/wch/r-source/blob/trunk/src/include/Rinternals.h
# http://www.maths.lth.se/matstat/staff/nader/stint/R_Manuals/R-ints.pdf
# https://github.com/wch/r-source/blob/trunk/src/main/serialize.c

everything <- function() {
    setClass("Person", representation(name = "character", age = "numeric"))

    list (
        NILSXP = NULL,
        SYMSXP = NULL,
        LISTSXP = list(a=1, 2, 3),
        CLOSXP = function(x, y) {},
        ENVSXP = new.env(),
        PROMSXP = NULL,
        LANGSXP = NULL,
        SPECIALSXP = NULL,
        BUILTINSXP = NULL,
        CHARSXP = "xyz",
        LGLSXP = TRUE,
        INTSXP = 1,
        REALSXP = 1.0,
        CPLXSXP = NULL,
        STRSXP = c("xyz", "abc"),
        DOTSXP = NULL,
        ANYSXP = NULL,
        VECSXP = NULL,
        EXPRSXP = NULL,
        BCODESXP = NULL,
        EXTPTRSXP = NULL,
        WEAKREFSXP = NULL,
        RAWSXP = raw(10),
        S4SXP = new("Person", name = "Hadley", age = 31),
        NEWSXP = NULL,
        FREESXP = NULL
    )
}

gen.data(everything, "everything")
gen.data(everything(), "result")
