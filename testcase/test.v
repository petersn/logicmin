
module circuit(
  input  wire [3:0] x,
  output wire [1:0] y
);
  wire a, b, c, d;
  wire t0, t1, t2, t3;

  assign a = x[0];
  assign b = x[1];
  assign c = x[2];
  assign d = x[3];

  // Intermediate random logic
  assign t0 = a ^ b;
  assign t1 = c & d;
  assign t2 = (~a & c) | (b & ~d);
  assign t3 = (a | d) & (~b | c);

  // Outputs
  assign y[0] = t0 ^ t1 ^ t2;
  assign y[1] = t3 ^ (b & c) ^ (~a & d);
endmodule

