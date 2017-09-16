class Cvc4 < Formula
  desc "Open-source automatic theorem prover for SMT"
  homepage "https://cvc4.cs.stanford.edu/"
  url "https://cvc4.cs.stanford.edu/downloads/builds/src/cvc4-1.5.tar.gz"
  sha256 "11ee2c3c182556a5ef750da9631191b3ad6c4ea592eb81d067a2edc41e57bd7b"

  depends_on "boost" => :build
  depends_on "gmp"
  depends_on "libantlr3c"
  depends_on "antlr@3"
  depends_on :arch => :x86_64

  def install
    args = ["--enable-static",
            "--enable-shared",
            "--with-compat",
            "--bsd",
            "--with-gmp",
            "--with-antlr-dir=#{Formula["libantlr3c"].opt_prefix}",
            "--prefix=#{prefix}"]
    system "./configure", *args
    system "make", "install"
  end

  test do
    (testpath/"simple.cvc").write <<-EOS.undent
      x0, x1, x2, x3 : BOOLEAN;
      ASSERT x1 OR NOT x0;
      ASSERT x0 OR NOT x3;
      ASSERT x3 OR x2;
      ASSERT x1 AND NOT x1;
      % EXPECT: valid
      QUERY x2;
    EOS
    result = shell_output "#{bin}/cvc4 #{(testpath/"simple.cvc")}"
    assert_match /valid/, result
    (testpath/"simple.smt").write <<-EOS.undent
      (set-option :produce-models true)
      (set-logic QF_BV)
      (define-fun s_2 () Bool false)
      (define-fun s_1 () Bool true)
      (assert (not s_1))
      (check-sat)
    EOS
    result = shell_output "#{bin}/cvc4 --lang smt #{(testpath/"simple.smt")}"
    assert_match /unsat/, result
  end
end
