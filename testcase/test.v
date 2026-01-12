// y[0] = (0x6af7ceaa >> x) & 1
// y[1] = (0x102e19a7 >> x) & 1

module circuit(
  input  wire [4:0] x,
  output reg [1:0] y
);
  always @(*) begin
    case (x)
      5'd0: y = 2'b10;
      5'd1: y = 2'b11;
      5'd2: y = 2'b10;
      5'd3: y = 2'b01;
      5'd4: y = 2'b00;
      5'd5: y = 2'b11;
      5'd6: y = 2'b00;
      5'd7: y = 2'b11;
      5'd8: y = 2'b10;
      5'd9: y = 2'b01;
      5'd10: y = 2'b01;
      5'd11: y = 2'b11;
      5'd12: y = 2'b10;
      5'd13: y = 2'b00;
      5'd14: y = 2'b01;
      5'd15: y = 2'b01;
      5'd16: y = 2'b01;
      5'd17: y = 2'b11;
      5'd18: y = 2'b11;
      5'd19: y = 2'b10;
      5'd20: y = 2'b01;
      5'd21: y = 2'b11;
      5'd22: y = 2'b01;
      5'd23: y = 2'b01;
      5'd24: y = 2'b00;
      5'd25: y = 2'b01;
      5'd26: y = 2'b00;
      5'd27: y = 2'b01;
      5'd28: y = 2'b10;
      5'd29: y = 2'b01;
      5'd30: y = 2'b01;
      5'd31: y = 2'b00;
    endcase
  end
endmodule

